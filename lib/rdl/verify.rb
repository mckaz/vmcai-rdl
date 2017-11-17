class RDL::CLine
  @lib = nil
  @fcount = 0
  EVAL_DATA = false

  def self.call(fstr, test=false)
    if EVAL_DATA
      fname = "translated#{@fcount}.rkt"
      @fcount = @fcount + 1
    else
      fname = "translated.rkt"
    end
    @lib = RDL::Verify.get_header if @lib.nil?
    fstr = "#{@lib}\n\n"+fstr+"\n\n"+pp_classids()
    File.open(fname, "w+") { |f| f.write fstr }
    ret = %x(racket #{fname})
    File.delete fname if ((test && !EVAL_DATA) || RDL::Verify.get_testing)
    #puts ret unless test
    ret
  end

  def self.pp_classids()
    str = "#|\n"
    str << "Class Name->Class ID\n"
    RDL.translate_ids.each { |kl, id| str << "#{kl}->#{id}\n" unless kl == :count }
    str << "|#"
  end

end


class RDL::Verify

  class VerifyError < StandardError ; end

  def self.set_use_assume(b)
    @use_assume = b
  end

  def self.set_testing(b)
    @testing = b
  end

  def self.get_testing
    @testing
  end
  
  USE_BV = false
  
  @BVSIZE = 6
  @fresh_id_counter = 0

  def self.BVSIZE
    @BVSIZE
  end

  def self.get_configs
    "(define USE_BV #{USE_BV})\n(define BVSIZE #{@BVSIZE})"
  end

  def self.is_native?(klass, meth)
    return (["Fixnum", "Bignum", "Integer", "Float", "Array", "Hash", "Kernel", "Enumerable"].include?(klass) || ["!=", "=="].include?(meth.to_s))
  end

  def self.kernel?(meth)
    ["class", "is_a?", "nil?"].include?(meth)
  end

  def self.touch_field(kl_scope, var, type)
    kl_scope = kl_scope.to_s
    var = var.to_s
    if RDL.translate_fields.include? kl_scope
      if RDL.translate_fields[kl_scope][var]
        #we're already done here
      else
        RDL.translate_fields[kl_scope][var] = type
      end
    else
      RDL.translate_fields[kl_scope] = {}
      RDL.translate_fields[kl_scope][var] = type #ast must have typechecked, so type of inst var is just type of assignment
    end
  end

  def self.verify_assert(klass, meth)
    # puts 'Reached verifier.'
    assertion = RDL.info.get klass, meth, :assert
    type = RDL.info.get klass, meth, :type
    raise RuntimeError, "Methods to be verified must include a type annotation (attempted to verify #{klass.to_s}.#{meth.to_s})" if type.nil?
    raise RuntimeError, "Methods to be verified may only include a single type annotation. (attempted to verify #{klass.to_s}.#{meth.to_s})" unless type.size == 1
    type = type[0]
    assert_ast = get_assert_ast assertion
    raise RuntimeError,"Can't verify method with no assertions?!" if assertion.nil?
    inst = RDL::Util.has_singleton_marker(klass.to_s).nil?
    ast = RDL::Typecheck.get_ast(klass, meth)

    ast_types = Hash.new

    RDL::Typecheck.typecheck(klass, meth, ast, ast_types)
    if ast.type == :def
      name, args, body = *ast
    elsif ast.type == :defs
      _, name, args, body = *ast
    elsif ast.type == :block
      meth_call, args, body = *ast
      _, def_name, _ = *meth_call
      name = meth
      raise RuntimeError, "Unexpected ast type #{ast.type} for ast #{ast}" unless (def_name == :define_method) || (def_name == :define_singleton_method) || (def_name == :rdl_define_method)
    else
      raise RuntimeError, "Unexpected ast type #{ast.type} for ast #{ast}"
    end
    argdefs = []
    arglist = "self "
    klass = RDL::Util.remove_singleton_marker(klass) if RDL::Util.has_singleton_marker klass 
    meths_todo = [[klass, meth, inst]]
    added = []
    meths_res = get_translated_meths(meths_todo, added)
    struct = "(struct object ([classid][objectid] "
    fields_added = ["classid", "objectid"]
    RDL.translate_fields.each_key { |kl|
      RDL.translate_fields[kl].each_key { |instvar| struct << "[#{instvar} #:auto #:mutable] " unless fields_added.include? instvar.to_s
                                          fields_added << instvar.to_s }} 
    struct << ") #:transparent #:auto-value (void))\n"

    block_name = "BLK" # default block name in case block is implicit
    args.children.each { |a|
      case a.type
      when :arg #normal argument
        arg_type = ast_types[a.children[0].object_id]
        argdefs << instantiate_sym_val(a.children[0], arg_type)
        arglist << a.children[0].to_s+" "
      when :blockarg  # if block is explicit paramter
        block_name = a.children[0].to_s
      else
        raise RuntimeError, "Arguments of type #{a.type} are not currently supported for verification."
      end
    }
    if type.block
      arglist << "#:block #{block_name}"
      argdefs << instantiate_sym_val(block_name, type.block) #type.block may be nil, in which case arg will be instantiated as (void)
    end

    argdefs << instantiate_struct("self", klass)
    klass = RDL::Util.add_singleton_marker(klass) if !inst
    assert_res = translate_assert(assert_ast, [klass, meth, inst], inst, klass, meth, arglist, block_name)
    meths_res = meths_res + get_translated_meths(RDL.translate_cache[[klass, meth, inst]][1], added)
    ret = ";;; OBJECT STRUCT:\n#{struct} \n;;; ARGUMENT DEFINITIONS:\n#{argdefs.join "\n"} \n;;; FUNCTION DEFINITIONS:\n"
    meths_res.each { |r| ret = ret + r }
    ret << assert_res
    ros_call = RDL::CLine.call(ret)
    name = make_name(klass, inst, meth)
    puts_result(name,ros_call)
    return ret
  end



  def self.verify_type(klass, meth)
    puts "Reached type verifier." unless @testing

    types = RDL.info.get klass, meth, :type
    raise RuntimeError, "No types given?? Cannot verify." if types.nil?
    raise RuntimeError, "Methods to be verified must only include a single type annotation (for now)." unless types.size == 1
    @use_assume = RDL.info.get(klass, meth, :assumes)[0]
    # Since we only support single types (i.e. no overloading), just take the first type
    typ = types[0]
    ret_type = typ.ret

    # inst = the method to verify is an instance method
    inst = RDL::Util.has_singleton_marker(klass.to_s).nil?

    raise RuntimeError, "Return type of method #{meth} is not a dependent type. Nothing to verify." unless ret_type.is_a? RDL::Type::DependentArgType
    klass = RDL::Util.remove_singleton_marker(klass) if RDL::Util.has_singleton_marker klass

    block_name = "BLK"   # TODO need to adjust

    # Translate relevant methods by seeding the worklist
    meths_todo = [[klass, meth, inst]]
    # This call is what does the real heavy lifting - passes off method translation
    added = []
    meths_res = get_translated_meths(meths_todo, added)

    ####################################################
    # GENERATE INIT CODE AND ASSUMES FOR EACH ARGUMENT #
    ####################################################

    arg_preds = [] # tracks annotations on argument types of each argument to the function
    arg_list = [] # track the names of each argument to the function to be verified
    arg_defs = [] # tracks the translated racket code for each argument's instantiation
    arg_def_info = [] # tracks info of args to be translated
    targs = {}

    if inst
      self_type = RDL::Type::NominalType.new(klass)
    else
      self_type = RDL::Type::SingletonType.new(RDL::Util.to_class(klass))
    end
    # Add a mapping for the self type to the type environment
    inst_map = {self: self_type}
    targs[:self] = self_type

    # Retrieve relevant information for each argument to the function to be verified
    typ.args.each { |arg|

      case arg
      when RDL::Type::DependentArgType
        n = arg.name
        arg_def_info << [n, arg.type.instantiate(inst_map)]
        targs[n.to_sym] = arg.type.instantiate(inst_map)

        # Dependent types are the only types that take predicates, so track here
        arg_preds << arg.predicate

      when RDL::Type::AnnotatedArgType
        n = arg.name
        arg_def_info << [n, arg.type.instantiate(inst_map)]
        targs[n.to_sym] = arg.type.instantiate(inst_map)
      else
        n = "fresh_arg"+@fresh_id_counter.to_s
        arg_def_info << [n, arg.instantiate(inst_map)]
        # Increment the fresh ID counter
        @fresh_id_counter += 1
      end

      # Push the argument name onto the argument list
      arg_list << n
    }

    ##############################################################
    # Translate dependent type predicates to Rosette assumptions #
    ##############################################################
    
    meths_todo = [] # If we run across more methods that need to be translated, we need to track them
    arg_list = arg_list.join ", " # Join the arguments by a comma to create ruby syntax

    # We join verification assumptions with (and) so that we can assume them all at verify time
    assume = "(and "

    # For each predicate received from the argument list, we need to parse the predicate into Racket
    arg_preds.each { |pred|
      to_parse = "def tmp(#{arg_list}) #{pred}; end" # necessary because we want arg names to be parsed as local vars, not as method calls
      ast = Parser::CurrentRuby.parse to_parse
      _, _, body = *ast
      ast_types = {}
      RDL::Typecheck.tc({}, RDL::Typecheck::Env.new(targs), body, ast_types)
      translated, _ = translate(body, ast_types, [klass, meth, inst], klass, inst, "block", false)
      assume << translated+" "
    }
    assume << ")"

    arg_list_tmp = (if arg_list.size > 0 then arg_list+",#{ret_type.name}" else "#{ret_type.name}" end)
    ast = Parser::CurrentRuby.parse "def tmpp(#{arg_list_tmp}) #{ret_type.predicate}; end"
    _, _, body = *ast
    ast_types = {}
    targs[ret_type.name.to_sym] = ret_type.type.instantiate(inst_map)
    RDL::Typecheck.tc({}, RDL::Typecheck::Env.new(targs), body, ast_types)
    assertion, _ = translate(body, ast_types, [klass, meth, inst], klass, inst, "block", false)
    meths_res = meths_res + get_translated_meths(RDL.translate_cache[[klass.to_s, meth, inst]][1], added)

    arg_list = "self "+arg_list.delete(",")
    arg_list << " #:block "+block_name if typ.block
    
    ##################################
    # BUILD OBJECT STRUCT DEFINITION #
    ##################################
    # This must be done after the method translation to accumulate necessary object fields

    struct = "(struct object ([classid][objectid] "
    fields_added = ["classid","objectid"]

    RDL.translate_fields.each_key { |kl|
      RDL.translate_fields[kl].each_key { |instvar| struct << "[#{instvar} #:auto #:mutable] " unless fields_added.include? instvar.to_s
                                          fields_added << instvar.to_s }} 
    struct << ") #:transparent #:auto-value (void))\n"

    ret_val = "(define #{ret_type.name} (#{klass}_#{'inst_' if inst}#{meth} #{arg_list}))\n"
    #    assertion = "(verify #:assume (assert #{assume}) #:guarantee (assert (let ([#{ret_type.name} (#{klass}_#{'inst_'if inst}#{meth} #{arg_list})]) (unless (stuck? #{ret_type.name}) #{assertion}))))"
    assertion = "(verify #:assume (assert #{assume}) #:guarantee (assert (unless (stuck? #{ret_type.name}) #{assertion})))"

    arg_defs << "  ; Initialize symbolic inputs to method "
    arg_def_info.each { |x, y| arg_defs << instantiate_sym_val(x, y) }
    arg_defs << "  ; Initialize struct self of type #{klass.to_s}"
    arg_defs << instantiate_struct("self", klass)

    arg_defs << instantiate_sym_val(block_name, typ.block) if typ.block

    ######################################################
    # Construct final string from constructed components #
    ######################################################

    ret = ";;; OBJECT STRUCT:\n#{struct} \n;;; ARGUMENT DEFINITIONS:\n#{arg_defs.join "\n"}\n\n;;; FUNCTION DEFINITIONS:\n"
    meths_res.each { |r| ret = ret + r }
    
    ret << ";;;RETURN VALUE:\n#{ret_val}\n;;;VERIFIED ASSERTION:\n#{assertion}"
    ros_call = RDL::CLine.call(ret)
    name = make_name(klass, inst, meth)
    puts_result(name,ros_call)
    @use_assume = false
    return ret
  end

  def self.make_name(klass,inst,meth)
    if (klass != "Object") then 
      "#{klass} #{if inst then 'instance' else 'singleton' end} "
    else
      ""
    end + "method #{meth}"
  end

  def self.puts_result(name,res)
    if (res != "(unsat)\n") then
      raise VerifyError, "#{name} is unsafe because #{res}" if @testing
      puts "#{name} is #{red("unsafe")} because #{res}"
    else 
      puts "#{name} is #{green("safe")}." unless @testing
      nil
    end
  end

  def self.red(txt)
    "\e[#{31}m#{txt}\e[0m"
  end

  def self.green(txt)
    "\e[#{32}m#{txt}\e[0m"
  end

  # ast is the AST to be translated
  # ast_types is a hash mapping the object_id of each expression in ast to its type
  # current_meth is a triplet [class, method, instance] identifying the method that is being translated. Note: `ast` may or may not be part of method code (see, e.g., translation of type refinements for modular verification)
  # kl_scope is the name of the class whose scope ast is in
  # inst is a bool telling us if `ast` comes from a singleton or instance method.
  # block_name is a string giving the name of the method block parameter, or "block" if no explicit parameter is provided
  # insert_ret is a boolean indicating whether a return statement should be inserted for this ast
  # use_types is a boolean indicating whether to translate methods which are called or to only use their types.
  # 
  def self.translate(ast, ast_types, current_meth, kl_scope, inst, block_name, insert_ret, use_types=false)
    raise "Can't translate nil ast." if ast.nil?
    case ast.type
    when :def, :defs
      if ast.type == :def
        name, args, body =  *ast
        inst_meth = true
      elsif ast.type == :defs
        _, name, args, body = *ast
        inst_meth = false
        kl_scope = RDL::Util.remove_singleton_marker(kl_scope) if RDL::Util.has_singleton_marker kl_scope ## should we do this?
      end
      argvars = []
      blk_expl = false # by default, assume block is not explicit
      args.children.each { |a|
        argvars.push a.children[0]
        if a.type == :blockarg
          block_name = a.children[0].to_s
          blk_expl = true
        end
      }
      argvars.push :block unless blk_expl #need to ensure that block name is reserved for method block
      insert_ret = !(name == :initialize)
      @dynmethvars = {}
      bodyres, defvars = translate(body, ast_types, [kl_scope.to_s, name, inst_meth], kl_scope, inst_meth, block_name, insert_ret)
      initvars = "(let ("
      defvars.each { |v| initvars << "[#{v} 'undefined]" unless argvars.include? v }
      initvars << ")"
      @dynmethvars.each { |k, v| initvars << instantiate_lvar(k, v, current_meth, kl_scope, inst, block_name) unless argvars.include?(k.to_sym) }
      @dynmethvars = {}      
      bodyres = "(begin\n#{bodyres} (return self))" if name == :initialize
      return ["(define (#{kl_scope}_#{'inst_'if inst_meth}#{name} self #{args_to_s(args.children)}#{' #:block [BLK (void)]' unless blk_expl})#{"\n\t" if initvars.size>0}#{initvars}\n\t#{bodyres}))\n",nil]
    when :begin
      res = "\t"
      vars = []
      ast.children.each_with_index { |c, i|
        if (i == ast.children.size - 1) && insert_ret # last element, want to insert return
          stmt, var = translate(c, ast_types, current_meth, kl_scope, inst, block_name, true)
        else
          stmt, var = translate(c, ast_types, current_meth, kl_scope, inst, block_name, false)
        end
        res << stmt + "\n\t"
        vars = vars | var
      }
      return ["(begin\n#{res})",vars]
    when :if
      cond, thenbr, elsebr = *ast
      res1, var1 = translate(cond, ast_types, current_meth, kl_scope, inst, block_name, false)
      if thenbr ## needed for `unless`
        res2, var2 = translate(thenbr, ast_types, current_meth, kl_scope, inst, block_name, insert_ret)
      else
        res2 = "(void)"
        var2 = []
      end
      res3, var3 = translate(elsebr, ast_types, current_meth, kl_scope, inst, block_name, insert_ret) if elsebr
      return ["(if #{res1} #{res2} #{res3})", var1|var2|var3] if elsebr
      if insert_ret
        ["(if #{res1} #{res2} (return (void)))", var1|var2]
      else
        ["(if #{res1} #{res2} (void))", var1|var2]
      end
    when :lvasgn
      var, rhs = *ast
      res, vars = translate(rhs, ast_types, current_meth, kl_scope, inst, block_name, false)
      #vars = [] if vars.nil?
      assert = (if RDL::Typecheck.lvarmap.has_key?(ast.object_id) then get_lvar_assert(var, RDL::Typecheck.lvarmap[ast.object_id], current_meth, kl_scope, inst, block_name) else "" end) # if lvar has a fixed type, assert refinement (if any)
      if insert_ret
        ["(begin (set! #{var.to_s} #{res}) #{assert} (return #{var.to_s}))",[var]| vars]
      else
        ["(begin (set! #{var.to_s} #{res}) #{assert} #{var.to_s})",[var]| vars]
      end
    when :lvar
      @dynmethvars[ast.children[0]] = RDL::Typecheck.lvarmap[ast.object_id] if RDL::Typecheck.lvarmap.has_key?(ast.object_id) # check if lvarmap (map from outer scope lvars to types) includes this lvar
      if insert_ret
        ["(return #{ast.children[0]})", []]
      else
        [ast.children[0].to_s, []]
      end
    when :ivasgn
      var, rhs = *ast
      touch_field(kl_scope, var, ast_types[ast.object_id])

      res, vars = translate(rhs, ast_types, current_meth, kl_scope, inst, block_name, false)
      if insert_ret
        ["(begin (set-object-#{var.to_s}! self #{res}) (return (object-#{var.to_s} self)))", vars]
      else
        ["(begin (set-object-#{var.to_s}! self #{res}) (object-#{var.to_s} self))", vars]
      end
    when :ivar
      var = ast.children[0].to_s
      touch_field(kl_scope, var, ast_types[ast.object_id])

      if insert_ret
        ["(return (object-#{ast.children[0].to_s} self))", []]
      else
        ["(object-#{ast.children[0].to_s} self)", []]
      end
    when :op_asgn
      if ast.children[0].type == :send
        rec, meth, *args = *ast.children[0]
        mutation_meth = (meth.to_s + '=').to_sym
        new_ast = ast.updated(:send, [rec, mutation_meth, *args, ast.updated(:send)])
        ast_types[new_ast.children[0].object_id] = ast_types[ast.children[0].children[0].object_id]
        #ast_types[new_ast.children[3].object_id]
        translate(new_ast, ast_types, current_meth, kl_scope, inst, block_name, insert_ret)
      else
        var_type = (if (ast.children[0].type == :lvasgn) then :lvar elsif (ast.children[0].type == :ivasgn) then :ivar else raise "unsupported type #{ast.children[0].type}" end)
        var = ast.children[0].updated var_type
        new_ast = ast.updated(ast.children[0].type, [ast.children[0].children[0], ast.updated(:send, [var, ast.children[1], ast.children[2]])])
        ast_types[new_ast.children[1].children[0].object_id] = ast_types[ast.children[0].object_id]
        translate(new_ast, ast_types, current_meth, kl_scope, inst, block_name, insert_ret)
      end
    when :masgn
      ## TODO: more complete behavior here. e.g., use of _ on LHS. 
      lhs, rhs = *ast
      res_rhs, vars = translate(rhs, ast_types, current_meth, kl_scope, inst, block_name, false)
      res = "(let ([rhs #{res_rhs}])(begin "
      count = 0
      lhs.children.each { |lhsvar|
        case lhsvar.type
        when :lvasgn
          var = lhsvar.children
          set = "set! #{var[0]} "
        when :ivasgn
          set = "set-object-#{lhsvar.children[0].to_s}! )"
          touch_field(kl_scope, var, RDL.info.get(kl_scope, lhsvar.children[0], :type))
        end
        vars = vars | var
        res << "(#{set} (Array_inst_fetch rhs #{count}))"
        count = count + 1
      }
      res << "))"
      if insert_ret
        ["(return #{res})", vars]
      else
        [res, vars]
      end
    when :send
      if use_types
        res, vars = translate_send_types(ast, ast_types, current_meth, kl_scope, inst, nil, block_name)
      else
        res, vars = translate_send(ast, ast_types, current_meth, kl_scope, inst, nil, block_name) # nil is for method block, which in :send case is not provided
      end
      if insert_ret
        ["(return #{res})", vars]
      else
        [res, vars]
      end
    when :block
      send_ast, bargs, bbody = *ast

      block_res, vars1 = translate(bbody, ast_types, current_meth, kl_scope, inst, block_name, true)
      lambda = "(lambda (#{args_to_s(bargs.children)})\n#{block_res})"
      res, vars2 = translate_send(send_ast, ast_types, current_meth, kl_scope, inst, lambda, block_name)
      vars = vars1 | vars2

      if insert_ret
        ["(return #{res})", vars]
      else
        [res, vars]
      end
    when :yield
      *args = *ast
      vars = []
      str = "(#{block_name} "
      args.each { |a|
        res, var = translate(a, ast_types, current_meth, kl_scope, inst, block_name, false)
        str << res + " "
        vars = vars | var
      }
      str << ")"
      if insert_ret
        ["(return #{str})", vars]
      else
        [str, vars]
      end
    when :return
      if ast.children.empty?
        ["(return (void))", []]
      else
        ret, vars = translate(ast.children[0], ast_types, current_meth, kl_scope, inst, block_name, false)
        ["(return #{ret})", vars]
      end
    when :array
      ary = "(Array_literal (list "

      ast.children.each{|c|
        if c.type == :splat
          raise "Array splat isn't supported yet"
        else
          ele, var = translate(c, ast_types, current_meth, kl_scope, inst, block_name, false)
          ary << ele + " "
        end

      }

      ary << "))"

      # Only supports empty init right now
      if insert_ret
        ["(return #{ary})", []]
      else
        [ary, []]
      end
    when :const
      ## Currently only supports classes
      name = resolve_class(ast)
      if !RDL.translate_ids.has_key?(name)
        classid = RDL.translate_ids[name] = RDL.translate_ids[:count]
        RDL.translate_ids[:count] = RDL.translate_ids[:count]+1
      else
        classid = RDL.translate_ids[name]
      end
      ret = "(let ([tmp (object #{RDL.translate_ids['Class']} #{classid})]) (begin (set-object-id! tmp #{classid}) tmp))"   # objectid will be same as classid so objectid will uniquely identify class
      if insert_ret
        ["(return #{ret})", []]
      else
        [ret, []]
      end
    when :hash
      #raise RuntimeError, "Reached maximum memory capcity. Unable to create hash corresponding to #{ast}." if @hash_mem_loc >= 9
      contents = "(list "
      ast.children.each { |p|
        #each child is a pair
        if p.type == :pair
          key, var1 = translate(p.children[0], ast_types, current_meth, kl_scope, inst, block_name, false)
          value, var2 = translate(p.children[1], ast_types, current_meth, kl_scope, inst, block_name, false)
          contents << "(cons #{key} #{value})"
        elsif p.type == :kwsplat
          # TODO
        else
          raise "Don't know what to do with #{p.type}"
        end
      }
      contents << ")"
      #str = "(new-hash #{@hash_mem_loc} #{contents})"
      if insert_ret
        ["(return (new_hash #{contents}))", var1|var2]
      else
        ["(new_hash #{contents})", var1|var2]
      end
    when :int
      ret = "(int #{ast.children[0]})"
      if insert_ret
        ["(return #{ret})", []]
      else
        [ret, []]
      end
    when :float
      ret = "(float #{ast.children[0]})"
      if insert_ret
        ["(return #{ret})", []]
      else
        [ret, []]
      end
    when :str
      if insert_ret
        ['(return "#{ast.children[0]}")', []]
      else
        ["\"#{ast.children[0]}\"", []]
      end
    when :nil
      if insert_ret
        ["(return (void))", []]
      else
        ["(void)", []]
      end
    when :self
      if insert_ret
        ["(return self)", []]
      else
        ["self", []]
      end
    when :true, :false
      if insert_ret
        ["(return #{ast.type})", []]
      else
        [ast.type.to_s, []]
      end
    when :and
      vars = []
      str = "(and "
      ast.children.each { |c|
        res, var = translate(c, ast_types, current_meth, kl_scope, inst, block_name, false)
        str << res+" "
        vars = vars | var
      }
      str << ")"
      if insert_ret
        ["(return #{str})", vars]
      else
        [str, vars]
      end
    when :or
      vars = []
      str = "(or "
      ast.children.each { |c|
        res, var = translate(c, ast_types, current_meth, kl_scope, inst, block_name, false)
        str << res+" "
        vars = vars | var
      }
      str << ")"
      if insert_ret
        ["(return #{str})", vars]
      else
        [str, vars]
      end
    else
      raise RuntimeError, "translation does not support ast #{ast} of type #{ast.type}"
    end   
  end

  def self.translate_send_types(rec, meth_info, current_meth, typ, mod, pure, meth_args, ast_types, kl_scope, inst, block, block_name)
    meth_klass, meth_name, meth_inst = *meth_info
    vars = []
    rec_type = rec_arg = nil
    if rec.nil?
      rec_type = nil
    else
      rec_type = ast_types[rec.object_id]
      raise RuntimeError, "can't find type of receiver #{rec}" if rec_type.nil?
    end
    if rec_type
      rec_arg, var = translate(rec, ast_types, current_meth, kl_scope, inst, "block", false)
      vars = vars | var
    end
    let = "(let ([self #{if rec_type then rec_arg else 'self' end}]"
    body = "(begin"
    arg_list = ""
    arg_typ_list = []
    targs = {}
    case rec_type
    when nil
      rec_type = (if meth_inst then RDL::Type::NominalType.new(meth_klass) else RDL::Type::SingletonType.new(meth_klass) end)
    when RDL::Type::SingletonType
      rec_type = RDL::Type::NominalType.new(rec_type.val) if meth_name == :new
    when RDL::Type::AnnotatedArgType, RDL::Type::DependentArgType
      rec_type = rec_type.type
    end

    inst_map = {:self => rec_type }
    targs[:self] = rec_type
    argnum = 0
    typ.args.each { |a|
      case a
      when RDL::Type::AnnotatedArgType, RDL::Type::DependentArgType
        n = a.name
        arg_list << n+", "
        arg_typ_list << a.type
        targs[n.to_sym] = a.type.instantiate(inst_map)
      else
        raise RuntimeError, "Please use annotated or dependent argument types for modularly verified methods. That is, name your arguments!"
      end
    }
    arg_list.chomp! ", "
    typ.args.each { |a|
      # assert the corrsponding meth_arg matches the spec for DependentArgTypes, skip for Nominal and AnnotatedTypes, raise error for rest (TODO: more arg types)
      case a
      when RDL::Type::AnnotatedArgType
        n = a.name
        arg, var = translate(meth_args[argnum], ast_types, current_meth, kl_scope, meth_inst, block_name, false)
        let << "[#{n} #{arg}]"
        vars = vars | var
        argnum = argnum + 1
      when RDL::Type::DependentArgType
        n = a.name
        arg, var = translate(meth_args[argnum], ast_types, current_meth, kl_scope, meth_inst, block_name, false)
        let << "[#{n} #{arg}]"
        vars = vars | var
        ast = Parser::CurrentRuby.parse "def tmp(#{arg_list}) #{a.predicate}; end"
        _, _, pred = *ast
        ast_types_tmp = {}
        RDL::Typecheck.tc({}, RDL::Typecheck::Env.new(targs), pred, ast_types_tmp)
        translated, var = translate(pred, ast_types_tmp, current_meth, meth_klass, meth_inst, "block", false)
        body << "(assert #{translated})"
        argnum = argnum + 1
      end
    }
    
    # mod is hash mapping method arguments (symbols) to a list of fields (symbols) which are modified by the method
    body << modify_fields(mod, targs)
    ret_type = typ.ret
    case ret_type
    when RDL::Type::DependentArgType
      n = ret_type.name
      targs[n.to_sym] = ret_type.type.instantiate(inst_map)
      arg_list_pre = arg_list.clone
      arg_list << (if arg_list.size > 0 then ", "+n else n end)
      ast = Parser::CurrentRuby.parse "def tmp(#{arg_list}) #{ret_type.predicate}; end"
      _, _, pred = *ast
      ast_types_tmp = {}
      RDL::Typecheck.tc({}, RDL::Typecheck::Env.new(targs), pred, ast_types_tmp)
      translated, _ = translate(pred, ast_types_tmp, current_meth, meth_klass, meth_inst, "block", false)
      body << (if pure then pure_meth_call(rec_type, meth_info, current_meth, arg_list_pre.split(","), arg_typ_list, ret_type, n) else instantiate_sym_val(n, ret_type.type.instantiate(inst_map)) end)  ### TODO: generate fresh name
      body << "(assume #{translated}) "
    when RDL::Type::AnnotatedArgType
      n = ret_type.name
      body << (if pure then pure_meth_call(rec_type, meth_info, current_meth, arg_list.split(","), arg_typ_list, ret_type, n) else instantiate_sym_val(n, ret_type.type.instantiate(inst_map)) end)
    else
      n = "tmpname"+@fresh_id_counter.to_s ### TODO: generate fresh name
      @fresh_id_counter = @fresh_id_counter+1
      body << (if pure then pure_meth_call(rec_type, meth_info, current_meth, arg_list.split(","), arg_typ_list, ret_type, n) else instantiate_sym_val(n, ret_type) end)
    end
    body << "#{n})"
    let << ")" + body + ")"
    [let, vars]
  end

  def self.pure_meth_call(rec_type, meth_info, current_meth, arg_names, arg_typs, ret_typ, ret_name)
    owner, meth_name, inst = *meth_info
    fun_name = "#{owner}_#{'inst_' if inst}#{meth_name}"
    if RDL.translate_cache[current_meth][1]
      RDL.translate_cache[current_meth][1] = RDL.translate_cache[current_meth][1] | [meth_info]
    else
      RDL.translate_cache[current_meth][1] = [meth_info]
    end
    #res = "(define-symbolic #{owner}_#{'inst_' if inst}#{meth_name} (~> integer? "  #first integer will be object-id of self
    #fun_type = "(~> integer? " # first integer will be object-id of self
    
    fun_type = "(~> "
    rec_type = rec_type.type if (rec_type.is_a?(RDL::Type::AnnotatedArgType) || rec_type.is_a?(RDL::Type::DependentArgType))
    rec_arg = "self"
    case rec_type
    when nil  # self is receiver
      rec_arg = "(object-objectid self)"
      fun_type << "integer? "
    when RDL::Type::UnionType
      if (rec_type == RDL.types[:integer])
        fun_type << (if USE_BV then "(bitvector #{@BVSIZE})" else "integer? " end)
        rec_arg = "(object-value #{rec_arg})"  # if rec is int, then get value from struct
      elsif (rec_type == RDL.types[:bool])
        fun_type << "boolean? "
      else
        raise RuntimeError, "Non-primitive union types are not permitted for uninterpreted functions."
      end
    when RDL::Type::NominalType
      if (rec_type == RDL.types[:float])
        fun_type << "real? "
        rec_arg = "(object-value #{rec_arg})"
      elsif (rec_type == RDL.types[:fixnum]) || (rec_type == RDL.types[:bignum])
      #fun_type << "integer? "
        fun_type << (if USE_BV then "(bitvector #{@BVSIZE})" else "integer? " end)
        rec_arg = "(object-value #{rec_arg})"  # if rec is int, then get value from struct
      else
        rec_arg = "(object-objectid #{rec_arg})"
        fun_type << "integer? "
      end
    when RDL::Type::SingletonType
      rec_arg = "(object-objectid #{rec_arg})"
      fun_type << "integer? "
    else
      raise RuntimeError, "not sure what to do with receiver type #{rec_type}"
    end
    ret_typ = ret_typ.type if (ret_typ.is_a?(RDL::Type::AnnotatedArgType) || ret_typ.is_a?(RDL::Type::DependentArgType))
    count = 0
    arg_typs.each { |t|
      t = t.type if (t.is_a?(RDL::Type::AnnotatedArgType) || t.is_a?(RDL::Type::DependentArgType))
      case t
      when RDL::Type::UnionType
        if (t == RDL.types[:integer])
          #fun_type << "integer? "
          fun_type << (if USE_BV then "(bitvector #{@BVSIZE})" else "integer? " end)
          arg_names[count] = "(object-value #{arg_names[count]})"
        elsif (t == RDL.types[:bool])
          fun_type << "boolean? "
        else
          raise RuntimeError, "Non-primitive union types are not permitted for uninterpreted functions."
        end
        count = count + 1
      when RDL::Type::NominalType
        if (t == RDL.types[:float])
          fun_type << "real? "
          arg_names[count] = "(object-value #{arg_names[count]})"
        elsif (t == RDL.types[:fixnum]) || (t == RDL.types[:bignum])
          #fun_type << "integer? "
          fun_type << (if USE_BV then "(bitvector #{@BVSIZE})" else "integer? " end)
          arg_names[count] = "(object-value #{arg_names[count]})"
        else
          arg_names[count] = "(object-objectid #{arg_names[count]})" # get objectid of object corresponding to this argument
          fun_type << "integer? "  # function arg will be an integer for objectid
        end
        count = count + 1
      else
        raise RuntimeError, "not sure what to do with arg type #{t}"
      end
    }

    case ret_typ
    when RDL::Type::UnionType
      if (ret_typ == RDL.types[:integer])
        #fun_type << "integer?)"
        fun_type << (if USE_BV then "(bitvector #{@BVSIZE}))" else "integer?)" end)
        ret_str = "(define #{ret_name} (int (#{fun_name} #{rec_arg} #{arg_names.join(' ')})))"
      elsif (ret_typ == RDL.types[:bool])
        fun_type << "boolean?)"
        ret_str = "(define #{ret_name} (#{fun_name} #{rec_arg} #{arg_names.join(' ')})) "
      else
        raise RuntimeError, "Non-primitive union types are not permitted for uninterpreted functions."
      end
    when RDL::Type::NominalType
      if (ret_typ == RDL.types[:float])
        fun_type << "real?)"
        ret_str = "(define #{ret_name} (float (#{fun_name} #{rec_arg} #{arg_names.join(' ')})))"
      elsif (ret_typ == RDL.types[:fixnum]) || (ret_typ == RDL.types[:bignum])
        #fun_type << "integer?)"
        fun_type << (if USE_BV then "(bitvector #{@BVSIZE}))" else "integer?)" end)
        ret_str = "(define #{ret_name} (int (#{fun_name} #{rec_arg} #{arg_names.join(' ')})))"
      else
        ## TODO
        klass_name = ret_typ.name.to_s
        if !RDL.translate_ids.has_key?(name)
          classid = RDL.translate_ids[name] = RDL.translate_ids[:count]
          RDL.translate_ids[:count] = RDL.translate_ids[:count]+1
        else
          classid = RDL.translate_ids[name]
        end
        fun_type << "integer?)"
        ret_str = "(define #{ret_name} (object #{classid} (#{fun_name} #{rec_arg} #{arg_names.join(' ')})))"
      end
    else
      raise RuntimeError, "not sure what to do with return type #{ret_typ}"
    end

    unless RDL.translate_cache.include?(meth_info)
      res = "(define-symbolic #{fun_name} #{fun_type})\n"
      if RDL.translate_cache[meth_info]
        RDL.translate_cache[meth_info][0] = res
      else
        RDL.translate_cache[meth_info] = []
        RDL.translate_cache[meth_info][0] = res
      end
    end
    return ret_str
  end


  def self.modify_fields(mod, targs)
    body = ""
    mod.each { |arg, fields|
      t = targs[arg]
      t = t.base if t.is_a?(RDL::Type::GenericType)
      case t
      when RDL::Type::NominalType
        mod_klass = t.name
      when RDL::Type::SingletonType
        mod_klass = (if (t.val.is_a?(Class) || (t.val.is_a?(Module))) then t.val.to_s else t.val.class.to_s end)
      when RDL::Type::TupleType
        mod_klass = "Array"
      when RDL::Type::FiniteHashType
        mod_klass = "Hash"
      else
        raise RuntimeError, "Not sure what to do with modifies arg of type #{t}"
      end

      if (fields == :havoc)
        raise RuntimeError, "havoc not yet implemented for modifies clause" #TODO
        unless RDL.translate_fields[mod_klass].nil?
          RDL.translate_fields[mod_klass].each { |field, type|
            n = "modified_#{field}_#{@fresh_id_counter}"
            @fresh_id_counter = @fresh_id_counter + 1 
            body << instantiate_sym_val(n, type)
            body << "(set-object-#{field}! #{arg} #{n})"
          }
        end
      elsif fields.is_a?(Array)
        fields.each { |f|
          klass_fields = RDL.translate_fields[mod_klass]
          klass_fields = RDL.translate_fields[mod_klass] = {} if klass_fields.nil?
          ftype = klass_fields[f]
          if ftype.nil?
            ftype = RDL.info.get(mod_klass, f, :type)
            raise RuntimeError, "No type information for class #{mod_klass} field #{f}" if ftype.nil?
            klass_fields[f] = ftype
          end
          fname = "modified_#{f}_#{@fresh_id_counter}"
          @fresh_id_counter = @fresh_id_counter + 1
          body << instantiate_sym_val(fname, ftype)
          body << "(set-object-#{f}! #{arg} #{fname})"
        }
      else
        raise RuntimeError, "Unknown modifies flag #{fields}"
      end
    }
    body
  end

  # like translate but for method calls. "block" argument contains either a lambda if a block was passed with the method call, or "(void)" if no block was given.
  def self.translate_send(ast, ast_types, current_meth, kl_scope, inst, block, block_name, rec_type=nil)

    receiver, meth_name, *meth_args = *ast

    vars = []

    return ["", vars] if meth_name == :instantiate!
    return ["", vars] if meth_name == :var_type
    return translate(ast.children[0], ast_types, current_meth, kl_scope, inst, block_name, false) if meth_name == :type_cast
    return ["(raze)", vars] if meth_name == :raise
    if meth_name == :exception?
      raise "Method arguments not expected for `exception?`. Got args #{meth_args}." if !meth_args.empty?
      raise "Expected receiver for method `exception?`." if receiver.nil?
      rec, vars = translate(receiver, ast_types, current_meth, kl_scope, inst, block_name, false)
      return ["(exception? #{rec})", vars]
    end

    orig_meth_name = meth_name.to_s
    meth_name = "ref" if meth_name == :[]
    meth_name = "refassign" if meth_name == :[]=  # TODO: will have to factor these out eventually

    #rec_type = receiver.nil? ? receiver : ast_types[receiver.object_id]
    if receiver.nil? then
      rec_type = nil
    else
      rec_type = ast_types[receiver.object_id] unless rec_type # if rec_type provided already, don't redefine it
      raise RuntimeError, "can't find type of receiver '#{receiver}' for method '#{orig_meth_name}' and args #{meth_args}" if rec_type.nil?
    end 
    rec_type = rec_type.type if (rec_type.is_a? RDL::Type::AnnotatedArgType) || rec_type.is_a?(RDL::Type::DependentArgType) ## TODO: change this once we start using meth specs
    case rec_type
    when nil
      # class or instance method within same or higher class
      if meth_name == :puts
        str = ""
        meth_args.each { |a|
          res, var = translate(a, ast_types, current_meth, kl_scope, inst, block_name, false)
          str << "(print #{res})" #one print statement for each puts argument
          vars = vars | var
        }
        return [str, vars]
      elsif meth_name == :block_given?
        return ["(void? #{block_name})", vars]
      end
      kl = Object.const_get(kl_scope) if kl_scope.is_a?(String)

      typ, mod, pure = check_use_type(kl, meth_name, inst)

      return translate_send_types(receiver, [kl.to_s, meth_name, inst], current_meth, typ, mod, pure, meth_args, ast_types, kl_scope, inst, block, block_name) if typ

      if inst
        kl = kl.instance_method(meth_name).owner if kl.instance_methods.include?(meth_name)
      else
        kl = kl.method(meth_name).owner.to_s if kl.methods.include?(meth_name)
        /#<Class:(.+)>/ =~ kl
        kl = Object.const_get($1)
      end


      
      if RDL.translate_cache[current_meth][1]
        RDL.translate_cache[current_meth][1] = RDL.translate_cache[current_meth][1] | [[kl.to_s, meth_name, inst]]
      else
        RDL.translate_cache[current_meth][1] = [[kl.to_s, meth_name, inst]]
      end

      str = "(#{kl}_#{'inst_' if inst}#{meth_name} self "
      meth_args.each { |a|
        res, var = translate(a, ast_types, current_meth, kl_scope, inst, block_name, false)
        str << res + " "
        vars = vars | var
      }
      str << (if block then "#:block #{block})" else ")" end)
      if @use_assume
        str = "(let ([tmp#{@fresh_id_counter} #{str}]) (begin (assume (not (stuck? tmp#{@fresh_id_counter}))) tmp#{@fresh_id_counter}))"   ## needed when calling methods which call assume
        @fresh_id_counter += 1
      end
      return [str, vars]

    when RDL::Type::SingletonType
      if rec_type.val.is_a? Class or rec_type.val.is_a? Module
        meth_class = rec_type.val
      elsif rec_type.val.is_a?(Symbol) && meth_name == :to_proc
        ### TODO
      else
        meth_class = rec_type.val.class
      end
      
      typ, mod, pure = check_use_type(meth_class, meth_name, false)

      return translate_send_types(receiver, [meth_class.to_s, meth_name, true], current_meth, typ, mod, pure, meth_args, ast_types, kl_scope, inst, block, block_name) if typ


      str_meth_class = meth_class.to_s
      if !RDL.translate_ids.has_key?(str_meth_class)
        classid = RDL.translate_ids[str_meth_class] = RDL.translate_ids[:count]
        RDL.translate_ids[:count] = RDL.translate_ids[:count]+1
      else
        classid = RDL.translate_ids[str_meth_class]
      end

      if meth_name == :new
        owner = meth_class.instance_method(:initialize).owner.to_s
        #Object.const_get(meth_class).instance_method(:initialize).owner # :initialize is considered instance_method
        meth_name = :initialize
        meth_inst = true
        slf = "(object #{classid} (new-obj-id))"
      elsif (meth_class == Fixnum) || (meth_class == Bignum)
      ## can reach this case for SingletonTypes, e.g. "1 <= ..."
        owner = "Integer"
        meth_inst = true
        slf, var = translate(receiver, ast_types, current_meth, kl_scope, inst, block_name, false)
        vars = vars | var
      elsif (meth_class == Float)
        owner = "Float"
        meth_inst = true
        slf, var = translate(receiver, ast_types, current_meth, kl_scope, inst, block_name, false)
        vars = vars | var
      else
        owner = meth_class.method(meth_name).owner.to_s
        /#<Class:(.+)>/ =~ owner
        owner = Object.const_get($1)   ## necessary because owner here is singleton class
        meth_inst = false
        slf = "(object #{classid} (new-obj-id))"
      end

      return ["(object #{classid} (new-obj-id))", vars] if (owner == BasicObject.to_s) && (meth_name == :initialize) # if initialize is defined in BasicObject, just return fresh object instance. may need to check for other core library classes.

      # We don't want to add the method to the worklist if it's a native library translation
      if RDL.translate_cache[current_meth][1]
        RDL.translate_cache[current_meth][1] = RDL.translate_cache[current_meth][1] | [[owner.to_s, meth_name, meth_inst]] if !is_native?(owner, meth_name)
      else
        RDL.translate_cache[current_meth][1] = [[owner.to_s, meth_name, meth_inst]] if !is_native?(owner, meth_name)
      end
      if (meth_name.to_s == "==" && owner != "Integer") 
         str = "(equal? #{slf} "
      elsif (meth_name.to_s == "!=" && owner != "Integer") 
        str = "(not_eq #{slf} "
      else
        str = "(#{owner}_#{'inst_' if meth_inst}#{meth_name} #{slf} "  ## TODO: is this the right self argument for singleton methods?
      end
      meth_args.each { |a|
        res, var = translate(a, ast_types, current_meth, kl_scope, inst, block_name, false)
        str << res + " "
        vars = vars | var
      }
      str << (if block then "#:block #{block})" else ")" end)
      if @use_assume && !is_native?(owner, meth_name)
        str = "(let ([tmp#{@fresh_id_counter} #{str}]) (begin (assume (not (stuck? tmp#{@fresh_id_counter}))) tmp#{@fresh_id_counter}))"   ## needed when calling methods which call assume
        @fresh_id_counter += 1
      end
      return [str, vars]

    when RDL::Type::NominalType

      typ, mod, pure = check_use_type(rec_type.klass, meth_name, true)

      return translate_send_types(receiver, [rec_type.klass.to_s, meth_name, true], current_meth, typ, mod, pure, meth_args, ast_types, kl_scope, inst, block, block_name) if typ
      owner = (if kernel?(orig_meth_name) then "Kernel" else rec_type.klass.instance_method(orig_meth_name).owner.to_s end)  ## Kernel methods unique in treating all methods as singletons
      orig_meth_name = meth_name
      if ["Fixnum", "Bignum", "Float", "Numeric", "BasicObject", "ActiveRecord::Core"].include?(owner) then
        if ((rec_type.klass.to_s == "Fixnum") || (rec_type.klass.to_s == "Bignum"))
          meth_name = "Integer_inst_#{meth_name}" # need this special case
        else
          meth_name, bl_exists = inst_method_dispatch(owner, meth_name, current_meth)
        end
      else
        # We don't want to add the method to the worklist if it's a native library translation
        if RDL.translate_cache[current_meth][1]
          RDL.translate_cache[current_meth][1] = RDL.translate_cache[current_meth][1] | [[owner.to_s, meth_name, true]] if !is_native?(owner, meth_name)
        else
          RDL.translate_cache[current_meth][1] = [[owner.to_s, meth_name, true]] if !is_native?(owner, meth_name)
        end
        if (meth_name.to_s == "==")
          meth_name = "equal?"
        elsif (meth_name.to_s == "!=")
          meth_name = "not_eq"
        else
          meth_name = "#{owner}_inst_#{meth_name}"
        end
      end

      slf, var = translate(receiver, ast_types, current_meth, kl_scope, inst, block_name, false)
      
      str = "(#{meth_name} #{slf} "
      
      meth_args.each { |a|
        res, var = translate(a, ast_types, current_meth, kl_scope, inst, block_name, false)
        str << res + " "
        vars = vars | var
      }
      str << (if block then "#:block #{block})" else ")" end)
      if @use_assume && !is_native?(owner, meth_name)
        str = "(let ([tmp#{@fresh_id_counter} #{str}]) (begin (assume (not (stuck? tmp#{@fresh_id_counter}))) tmp#{@fresh_id_counter}))"   ## needed when calling methods which call assume
        @fresh_id_counter += 1
      end
      return [str, vars]
    when RDL::Type::UnionType
      if rec_type == RDL.types[:bool]
        meth_name = "and" if meth_name == :&
        meth_name = "or" if meth_name == :|
        meth_name = "xor" if meth_name == :^
        meth_name = "eq?" if meth_name == :==
        rec_arg, var = translate(receiver, ast_types, current_meth, kl_scope, inst, block_name, false)
        vars = vars | var
        str = "(#{meth_name} #{rec_arg} "
        meth_args.each { |a|
          res, var = translate(a, ast_types, current_meth, kl_scope, inst, block_name, false)
          str << res+" "
          vars = vars | var
        } 
        str << ")"
        return [str, vars]
      elsif rec_type == RDL.types[:integer]
        meth_name = "Integer_inst_#{meth_name}"
        rec_arg, var = translate(receiver, ast_types, current_meth, kl_scope, inst, block_name, false)
        vars = vars | var
        str = "(#{meth_name} #{rec_arg} "
        meth_args.each { |a|
          res, var = translate(a, ast_types, current_meth, kl_scope, inst, block_name, false)
          str << res+" "
          vars = vars | var
        } 
        str << ")"
        return [str, vars]
      else
        union_types = rec_type.types
        rec_arg, vars = translate(receiver, ast_types, current_meth, kl_scope, inst, block_name, false)
        str = "(cond "
        union_types.each { |t|
          id = get_class_id(t)
          meth_call, var = translate_send(ast, ast_types, current_meth, kl_scope, inst, block, block_name, t) # call translate_send with t, type of object corresponding to id
          ## TODO: change below after switching to using structs for numerics
          str << (if id.is_a?(String) then "[(#{id} #{rec_arg}) #{meth_call}]" else "[(= #{id} (object-classid #{rec_arg})) #{meth_call}]" end )# dispatch method class to call corresponding to receiver's object-classid
          vars = vars | var
        }
        str << ")"
        [str, vars]
      end
    when RDL::Type::GenericType
      # translate method call using base of generic type
      translate_send(ast, ast_types, current_meth, kl_scope, inst, block, block_name, rec_type.base)

    when RDL::Type::TupleType
      # Need to use the original name to do classname lookup
      owner = Array.instance_method(orig_meth_name).owner.to_s
      
      #This is kinda temporary jank, doesn't handle updating the meths list for non-native code
      meth_name = "Array_inst_#{meth_name}"
      receiver_translation, var = translate(receiver, ast_types, current_meth, kl_scope, inst, block_name, false)
      vars = vars | var
      str = "(#{meth_name} #{receiver_translation} "

      meth_args.each{|a|
        res, var = translate(a, ast_types, current_meth, kl_scope, inst, block_name, false)
        str << res + " "
        vars = vars | var
      }

      str << (if block then "#:block #{block})" else ")" end)

      [str, vars]

    when RDL::Type::FiniteHashType
      owner = Hash.instance_method(orig_meth_name).owner.to_s
      meth_name, bl_exists = inst_method_dispatch(owner, meth_name, current_meth)
      rec_arg, var = translate(receiver, ast_types, current_meth, kl_scope, inst, block_name, false)
      vars = vars | var
      str = "(#{meth_name} #{rec_arg} "
      meth_args.each { |a|
        res, var = translate(a, ast_types, current_meth, kl_scope, inst, block_name, false)
        str << res+" "
        vars = vars | var
      }
      str << (if bl_exists then "#:block #{block})" else ")" end)

      [str, vars]

    else
      raise RuntimeError, "translation does not yet support method calls on receivers of type #{rec_type} where type has class #{rec_type.class} (attempted to call #{meth_name})"
    end
  end

  ## similar to look up, checks if modular flag is set to true for type in this or ancestors class
  def self.check_use_type(meth_class, meth_name, inst)
    if inst
      meth_lookup = meth_name.to_s
    else
      if meth_name == :new
        meth_lookup = "initialize"
      else
        meth_lookup = 'self.'+meth_name.to_s
      end
    end
    typ = mod = p = nil
    if meth_class.instance_of?(Module)
      anc = Module.ancestors
    else
      anc = []
    end
    (meth_class.ancestors + anc).each { |kl|
      if (typs = RDL.mixin_types[kl])
        typs.each { |meth, t, wrap, typecheck, verify, modifies, pure|
          if meth_lookup == meth.to_s
            typ = t
            mod = modifies
            p = pure
          end
        }
      end
    }

    return [typ, mod, p]

  end

  # given a (non-union) type t, returns class id corresponding to class of type
  def self.get_class_id(t)
    case t
    when RDL::Type::NominalType
      id = RDL.translate_ids[t.name]
    when RDL::Type::SingletonType
      id = RDL.translate_ids[t.val.to_s]
    when RDL::Type::FiniteHashType
      id = RDL.translate_ids["Hash"]
    else
      raise RuntimeError, "Can't find class ID corresponding to type #{t}"
    end
    raise RuntimeError, "No class ID corresponding to #{t} found" if id.nil?
    id
  end

  def self.rewrite_name(name)
    name.gsub!("[]", "ref")
    name.gsub!("=", "assign")
    name
  end

  def self.inst_method_dispatch(owner, meth, current_meth)
    case owner
    when "Fixnum", "Bignum"
      meth = "Integer_inst_#{meth}"
      [meth, false]
    when "Float"
      meth = "Float_inst_#{meth}"
      [meth, false]
    when "Numeric"
      meth = "=" if meth == :==
      meth = "-" if meth == :-@
      meth = "modulo" if meth == :%
      #meth = "not_eq" if meth == :!=
      [meth, false]
    when "Hash"
      inst_hash_dispatch(meth)
    when "Array"
      inst_array_dispatch(meth)
    when "BasicObject"
      meth = "not_eq" if meth == :!= ## for some reason, sometimes numeric meth :!= has owner BasicObject, sometimes it doesn't
      meth = "equal?" if meth == :==
      [meth, false]
    when "ActiveRecord::Core"
      meth = "obj-id-eq" if meth == :==
    else
      ## should only reach this case when user has defined their own method for a core class
      if RDL.translate_cache[current_meth][1]
        RDL.translate_cache[current_meth][1] = RDL.translate_cache[current_meth][1] | [[owner.to_s, meth, true]]
      else
        RDL.translate_cache[current_meth][1] = [[owner.to_s, meth, true]]
      end
      ["#{owner}_inst_#{meth}", true]
    end
  end

  # this method translates the provided assertion block
  # ast is the block node of the call to assert
  # inst_meth is a boolean indicating whether the method the assertion is over is an instance method
  # klass is the class of the method the assertion is over
  # meth is the name of the method the assertion is over
  # arglist is a string list of the arguments to the method
  def self.translate_assert(ast, current_meth, inst_meth, klass, meth, arglist, block_name)
    _, args, body = *ast

    # much of the below is lifted from RDL::Typecheck.typecheck
    ast_types = {}
    meth_type = RDL.info.get(klass, meth, :type)[0] ## [0] because I'm presuming just one type for now
    #arg_types = meth_type.args << meth_type.ret ## append ret arg because ret is part of block
    type = RDL::Type::MethodType.new(meth_type.args + [meth_type.ret], nil, RDL.types[:bool])
    if RDL::Util.has_singleton_marker(klass)
      # to_class gets the class object itself, so remove singleton marker to get class rather than singleton class
      self_type = RDL::Type::SingletonType.new(RDL::Util.to_class(RDL::Util.remove_singleton_marker(klass)))
    else
      self_type = RDL::Type::NominalType.new(klass)
    end
    inst = {self: self_type}
    type = type.instantiate inst
    _, targs = RDL::Typecheck.args_hash({}, RDL::Typecheck::Env.new, type, args, ast, 'block', ast_types)
    targs[:self] = self_type
    scope = { tret: RDL.types[:bool], tblock: nil, captured: Hash.new, context_types: RDL.info.get(klass, meth, :context_types) }
    begin
      old_captured = scope[:captured].dup
      if body.nil?
        body_type = RDL.types[:nil]
      else
        _, body_type = RDL::Typecheck.tc(scope, RDL::Typecheck::Env.new(targs.merge(scope[:captured])), body, ast_types)
      end
    end until old_captured == scope[:captured]
    RDL::Typecheck.error :bad_return_type, [body_type.to_s, type.ret.to_s], body unless body.nil? || body_type <= type.ret    

    res,_ = translate(body, ast_types, current_meth, klass, inst, block_name, false) # TODO: need to check on proper inst arg here
    klass = RDL::Util.remove_singleton_marker(klass) if RDL::Util.has_singleton_marker klass
    retdef = "(define ret (#{klass}_#{'inst_'if inst_meth}#{meth} #{arglist}))\n"
    res = "(verify (assert #{res}))"
    return retdef+res
  end

  def self.get_translated_meths(meths_todo, added)
    return [] if meths_todo.nil?
    res = []
    # Hacky way to drive the worklist until empty
    meths_todo.each { |kl, mth, ins|
      kl = kl.to_s
      if added.include? [kl, mth, ins]
      # Method has already been added to translated program, do nothing
      elsif RDL.translate_cache.include? [kl, mth, ins]
        # If it was in the cache, just retrieve it
        res << RDL.translate_cache[[kl, mth, ins]][0]
        #res << RDL.translate_cache[[kl, mth, ins]]
        added << [kl, mth, ins]
        res = res + get_translated_meths(RDL.translate_cache[[kl, mth, ins]][1], added)
      else
        # Type coercion and strip singleton marker
        if !ins && !RDL::Util.has_singleton_marker(kl)
          kl_marked = RDL::Util.add_singleton_marker(kl)
        else
          kl_marked = kl
        end
        mth = mth.to_sym
        RDL.translate_cache[[kl, mth, ins]] = []

        # Get this method's AST to translate it
        ast = RDL::Typecheck.get_ast(kl_marked, mth)

        # Build AST type hash with typechecker call (maps object IDs to their types)
        ast_ty = Hash.new
        RDL::Typecheck.typecheck(kl_marked, mth.to_sym, ast, ast_ty)

        RDL.translate_cache[[kl, mth, ins]][0] = "(void)"
        #RDL.translate_cache[[kl, mth, ins]] = "(void)"  # need to temporarily fill this index to handle recursive methods
        if (ast.type == :block)
          # for dynamically defined methods
          meth_call, _, _ = *ast
          _, def_name, _ = *meth_call
          raise RuntimeError, "Unexpected ast type #{ast.type} for ast #{ast}" unless (def_name == :define_method) || (def_name == :define_singleton_method) || (def_name == :rdl_define_method)
          name = mth.to_sym
          ast = ast.updated((if(ins) then :def else :defs end), [name, ast.children[1], ast.children[2]])
        end

        # tmpres is the string for the translated method
        tmpres, _ = translate(ast, ast_ty, [kl, mth, ins], kl, ins, "BLK", true)
        # For actually adding to the output string, we want a newline for readability in the output
        res << tmpres+"\n"
        # Save the unmodified translation in the cache
        RDL.translate_cache[[kl, mth, ins]][0] = tmpres
        #RDL.translate_cache[[kl, mth, ins]] = tmpres
        added << [kl, mth, ins]
        res = res + get_translated_meths(RDL.translate_cache[[kl, mth, ins]][1], added)
      end

      true
    }
    return res
  end

  def self.translate_refinement(name, t, current_meth, klass, inst, block_name)
    raise "Expected DependentArgType, got #{t}." unless t.instance_of?(RDL::Type::DependentArgType)
    targs = {}
    if inst
      self_type = RDL::Type::NominalType.new(klass)
    else
      self_type = RDL::Type::SingletonType.new(RDL::Util.to_class(RDL::Util.remove_singleton_marker(klass)))
    end
    inst_map = {self: self_type}
    targs[:self] = self_type
    targs[name] = t.type.instantiate(inst_map)
    to_parse = "def tmp(#{name}) #{t.predicate}; end" # necessary because we want arg names to be parsed as local vars, not as method calls
    ast = Parser::CurrentRuby.parse to_parse
    ast_types = {}
    _, _, body = *ast
    RDL::Typecheck.tc({}, RDL::Typecheck::Env.new(targs), body, ast_types)
    translated, _ = translate(body, ast_types, current_meth, klass, inst, block_name, false)
    return translated
  end
  
  def self.get_lvar_assert(name, t, current_meth, klass, inst, block_name)
    case t
    when RDL::Type::DependentArgType
      "(assert #{translate_refinement(name, t, current_meth, klass, inst, block_name)})"
    else
      "" # nothing to assert here
    end
  end

  def self.instantiate_lvar(name, t, current_meth, klass, inst, block_name)
    case t
    when RDL::Type::DependentArgType
      raise RuntimeError, "Please name annotated argument types the same as the variables they are annotating. Given variable #{name} but annotated name #{t.name}." unless name.to_sym == t.name.to_sym
      symval = instantiate_sym_val(name, t.type)
      symval << "(assume #{translate_refinement(name, t, current_meth, klass, inst, block_name)})"
      symval
    else
      instantiate_sym_val(name, t)
    end
  end
                            
  # instantiates a new object struct
  # name is name given to struct
  # klass is the class of the struct
  # deep is level of struct. needed to bound mutually recursive calls between this and instantiate_sym_val
  def self.instantiate_struct(name, klass, deep = 0)

    # If we need a new ID to represent this class, generate one
    unless RDL.translate_ids.has_key? klass.to_s
      RDL.translate_ids[klass.to_s] = RDL.translate_ids[:count]
      RDL.translate_ids[:count] = RDL.translate_ids[:count]+1
    end

    # Start out by opening the definition and creating the base object
    argdefs = []

    klass = Object.const_get(klass) if klass.is_a? String

    argdefs << "(define #{name}"
    argdefs << (if klass.instance_of?(Module) then "(let () (define-symbolic* classid integer?) (let ([#{name} (object classid (new-obj-id))])" else "(let ([#{name} (object #{RDL.translate_ids[klass.to_s]} (new-obj-id))])" end)  # if klass is a module, leave classid as sym int, since object instance's class depends on where module is included. Extra let is included to allow us to call define-symbolic, since we can't call it in an expression context (hacky).

    # WARNING/TODO: This approach of separating inits from sets assumes that
    # instantiate_sym_value only performs definitions and no additional processing
    arginits = []
    argsets = []

    # If there are fields to translate, instantiate and set each one into the object
    unless deep > 2
      if RDL.translate_fields[klass.to_s]
        RDL.translate_fields[klass.to_s].each { |instvar, type|
          arginits << instantiate_sym_val(instvar, type, false, deep)
          argsets << "(set-object-#{instvar}! #{name} #{instvar})"
        }
      end
    end

    # After building all the fields, yield the actual constructed object as the value to bind
    # First put all inits (i.e. define and define-symbolic calls to maintain body context)
    # Then put the actual sets to switch into expression context after done with definitions
    argdefs = argdefs + arginits + argsets
    argdefs << "#{name}))"
    argdefs << ")" if klass.instance_of? Module # one more to close the extra let above
    return argdefs.join "\n"
  end


  # instantiates a single symbolic or object struct argument
  # name is the name given to the argument
  # type is the RDL type of the argument
  # deep is level of struct. needed to bound mutually recursive calls between this and instantiate_sym_val
  def self.instantiate_sym_val(name, type, comment = true, deep = 0)
    type = type.type if (type.is_a?(RDL::Type::DependentArgType) || type.is_a?(RDL::Type::AnnotatedArgType))
    str = case type
          when RDL::Type::NominalType
            if type.klass == Fixnum || type.klass == Bignum
              if USE_BV
                "(define #{name} (begin (define-symbolic* bv_#{name} (bitvector #{@BVSIZE})) (int bv_#{name})))\n"
              else
                "(define #{name} (begin (define-symbolic* #{name} integer?) (int #{name})))\n"
              end
            elsif type.klass == Float
              "(define #{name} (begin (define-symbolic* real_#{name} real?) (float real_#{name})))\n"
            elsif type.klass == Array
              "(define #{name} (new-symbolic-array))"
            else
              instantiate_struct(name, type.name, deep + 1)
            end
          when RDL::Type::UnionType
            if type == RDL.types[:bool]
              "(define-symbolic* #{name} boolean?)\n"
            elsif type == RDL.types[:integer]
              if USE_BV
                "(define #{name} (begin (define-symbolic* bv_#{name} (bitvector #{@BVSIZE})) (int bv_#{name})))\n"
              else
                "(define #{name} (begin (define-symbolic* #{name} integer?) (int #{name})))\n"
              end
            else
              #other union type, need to deal with
              raise RuntimeError, "non boolean or integer symbolic union types not currently supported. got type #{type} and name #{name}"
            end
          when RDL::Type::TupleType
            # Translate all tuple types as simply empty array initializations
            "(define #{name} (Array_literal (list)))"
          when RDL::Type::GenericType
            # If this is a generic array, populate with symbolic members
            if type.base.is_a?(RDL::Type::NominalType) && type.base.klass == Array
              element_builder = instantiate_sym_val("__CONSTRUCTED_ELE", type.params[0], false)
              "(define #{name}\n(new-symbolic-array\n(lambda (__IDX)\n#{element_builder}\n(return __CONSTRUCTED_ELE))))"
            else
              # Pass down the base of the type for verification - type erasure!
              result = instantiate_sym_val(name, type.base, comment)
              comment = false
              result
            end
          when RDL::Type::MethodType
          when nil
            type = "nil"
            "(define #{name} (void))"
          else raise RuntimeError, "unsupported argument type #{type} for argument named #{name}"
          end
    
    (comment ? "  ; Initialize #{name} of type #{type}\n" : "") + str
  end


  def self.resolve_class(ast)
    if !ast.respond_to?(:children)
      return ast.to_s
    elsif ast.type == :const
      scope = resolve_class(ast.children[0])
      klass = resolve_class(ast.children[1])
      return scope+"::"+klass if scope
      return klass
    elsif ast.type == :lvar
      ### TODO: check on this
      return ast.children[0].to_s
    end
  end

  def self.args_to_s(args)
    string = ""
    args.each {|a|
      if a.type == :blockarg
        string << "#:block [#{a.children[0]} (void)]"
      elsif a.equal? args.last
        string << a.children[0].to_s
      elsif a.equal? args.first
        string << " "+a.children[0].to_s+" "
      else
        string << a.children[0].to_s+" "
      end
    }
    return string
  end

  def self.get_assert_ast(assertion)
    file, line = assertion[0].source_location
    raise Runtime Error, "verification in irb not supported" if file == "(irb)"
    raise Runtime Error, "verification in pry not supported, for now" if file == "(pry)"
    #TODO: Once pending assertions is worked out: Parser::CurrentRuby.parse Pry::Code.from_method(assertion[0])

    digest = Digest::MD5.file file
    cache_hit = ((RDL.parser_cache.has_key? file) &&
                 (RDL.parser_cache[file][0] == digest))
    unless cache_hit
      file_ast = Parser::CurrentRuby.parse_file file
      mapper = RDL::Typecheck::ASTMapper.new(file)
      mapper.process(file_ast)
      cache = {ast: file_ast, line_defs: mapper.line_defs}
      RDL.parser_cache[file] = [digest, cache]
    end
    ast = RDL.parser_cache[file][1][:line_defs][line]
    raise RuntimeError, "Can't find source for assertion" if ast.nil?
    return ast
  end

  def self.get_header
    path = File.expand_path("../verif_libraries",__FILE__)
    ivl = path+"/ivl.rkt"
    lib_dir = Dir.glob(path+"/*.rkt")
    racket_libs = "(require racket/include)(require racket/undefined)"
    fstr = "#lang s-exp (file \"#{ivl}\")\n#{racket_libs}\n"
    fstr << get_configs
    #fstr = "#lang rosette/safe\n(require racket/include)\n"
    lib_dir.each { |fn|
      fstr << '(include (file "'+fn+'"))'+"\n" unless (fn == ivl)# include every file in the verif_libraries directory
    }
    fstr
  end


  def self.get_ast(klass, meth, inst)
    #file, line = $__rdl_info.get(klass, meth, :source_location)
    klass = Object.const_get(klass) if klass.is_a? String
    if inst
      file, line = klass.instance_method(meth.to_sym).source_location
    else
      file, line = klass.method(meth.to_sym).source_location
    end
    raise RuntimeError, "No file for #{RDL::Util.pp_klass_method(klass, meth)}" if file.nil?
    raise RuntimeError, "static type checking in irb not supported" if file == "(irb)"
    if file == "(pry)"
      # no caching...
      if RDL::Wrap.wrapped?(klass, meth)
        meth_name = RDL::Wrap.wrapped_name(klass, meth)
      else
        meth_name = meth
      end
      if inst
        the_meth = RDL::Util.to_class(klass).instance_method(meth_name)
      else
        the_meth = RDL::Util.to_class(klass).method(meth_name)
      end
      code = Pry::Code.from_method the_meth
      return Parser::CurrentRuby.parse code.to_s
    end

    digest = Digest::MD5.file file
    cache_hit = ((RDL.parser_cache.has_key? file) &&
                 (RDL.parser_cache[file][0] == digest))
    unless cache_hit
      file_ast = Parser::CurrentRuby.parse_file file
      mapper = RDL::Typecheck::ASTMapper.new(file)
      mapper.process(file_ast)
      cache = {ast: file_ast, line_defs: mapper.line_defs}
      RDL.parser_cache[file] = [digest, cache]
    end
    ast = RDL.parser_cache[file][1][:line_defs][line]
    raise RuntimeError, "Can't find source for class #{RDL::Util.pp_klass_method(klass, meth)}" if ast.nil?
    return ast
  end

end







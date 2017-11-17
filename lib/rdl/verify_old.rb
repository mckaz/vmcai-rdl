class RDL::SymbolicValue
  attr_reader :name
  
  def initialize(name)
    @name = name.to_s
  end
end

class RDL::SymbolicObject
  attr_accessor :state
  attr_accessor :klass

  
  def initialize(state={},klass=nil)
    @state = state
    @klass = klass
  end
end

class SymArray
  attr_accessor :contents

  def initialize(contents=nil)
    @contents = contents
  end

  def type
    :symarray
  end
end

class RDL::Verify

  def self.verify(klass, meth)
    puts "Reached verifier."
    assertion = $__rdl_info.get(klass, meth, :assert)
    ast = RDL::Typecheck.get_ast(klass,meth)
    raise RuntimeError, "Can't verify method with no assertions?!" if assertion.nil?

    if ast.type == :def
      name, args, body = *ast
    elsif ast.type == :defs
      _, name, args, body = *ast
    else
      raise RuntimeError, "Unexpected ast type #{ast.type}"
    end

    argsHash = {}
    args.children.each { |a|  argsHash[a.children[0]] = RDL::SymbolicValue.new(a.children[0]) }
    argsHash[:ret] = nil
    symEx = symbolic_exec(argsHash, [Parser::CurrentRuby.parse("true")], body, klass)
    return symEx
  end

  def self.symbolic_exec(state, pathcond, code, klass)
    if (code.type == :lvasgn) || (code.type == :ivasgn)
      var,rhs = *code
      #paths = symbolic_exec(state.clone, pathcond.clone, rhs, klass)
      paths = symbolic_exec state,pathcond,rhs,klass
      results = []
      paths.each { |state, pathcond|
        rhs = state[:ret]
        rhs = replace_vars rhs,state,klass
        #state[var]=state[:ret]=rhs
        state = state.merge({:ret=>rhs,var=>rhs})
        results.push [state,pathcond]
      }
      return results
      
    elsif code.type == :begin
      paths = [[state, pathcond]]
      code.children.each { |c| next_paths = []
        #paths.each { |st,pc| next_paths.concat(symbolic_exec(st.clone, pc.clone, c, klass)) }
        paths.each { |st,pc| next_paths.concat(symbolic_exec(st,pc,c,klass)) }
        paths = next_paths
      }
      return paths
    elsif code.type == :if
      cond = replace_vars(code.children[0], state, klass)
      neg_cond = cond.updated(:send,[cond,:!])
      then_branch = code.children[1]
      else_branch = code.children[2]
      #first_sym = symbolic_exec(state.clone, pathcond+[cond], then_branch, klass)
      first_sym = symbolic_exec state,pathcond+[cond],then_branch,klass
      if else_branch
        #second_sym = symbolic_exec(state.clone,pathcond+[neg_cond],else_branch, klass)
        second_sym = symbolic_exec state,pathcond+[neg_cond],else_branch,klass
      else
        second_sym = [[state.merge(ret:nil),pathcond+[neg_cond]]]
      end
      return first_sym+second_sym
    elsif code.type == :return
      #paths = symbolic_exec(state.clone, pathcond.clone, code.children[0], klass)
      paths = symbolic_exec state,pathcond,code.children[0],klass
      return paths
    elsif code.type==:ivar
      var = code.children[0]
      if state.include?(var)
        #state[:ret] = replace_vars(code,state,klass)
        state = state.merge({:ret => replace_vars(code,state,klass)})
      else
        klass = Object.const_get(klass) if klass.is_a?(String)
        #state[:ret] = klass.instance_variable_get(var)
        state = state.merge({:ret=>klass.instance_variable_get(var)})
      end
      return [[state,pathcond]]
    elsif code.type== :array
      if code.children.size>0
        *vals = *code.children
        results = []
        #state[:ret] = []
        state = state.merge({:ret => []})
        #paths = [[state,pathcond]]
        paths = [[state,pathcond]]
        vals.each_with_index {|v,i|
          next_paths = []
          #paths.each { |st,pc| next_paths.concat(symbolic_exec(st.clone,pc.clone,v,klass))
          paths.each { |st,pc| next_paths.concat(symbolic_exec(st,pc,v,klass)) 
            next_paths.each { |next_st,next_pc| next_st[:ret] = AST::Node.new(:store,[st[:ret],Parser::CurrentRuby.parse(i.to_s),next_st[:ret]])
              #next_st = next_st.merge({:ret => AST::Node.new(:store,[st[:ret],Parser::CurrentRuby.parse(i.to_s),next_st[:ret]])})
              if ((i+1)==vals.size) then next_st[:ret] = SymArray.new(next_st[:ret]) end
              #next_st = next_st.merge({:ret => SymArray.new(next_st[:ret])}) if (i+1)==vals.size
            }
            paths = next_paths
          }
        }
        ### need to test that this works with new mutation approach
          return paths
      else
        #state[:ret] = SymArray.new([])
        state = state.merge( {:ret => SymArray.new([])} )
        return [[state,pathcond]]
      end
    elsif code.type==:lvar || code.type==:true || code.type==:false || code.type==:int || code.type==:float || code.type == :symarray
      #state[:ret] = replace_vars(code,state,klass)
      state = state.merge({:ret => replace_vars(code,state,klass)})
      return [[state,pathcond]]
    elsif (code.type==:send) & (code.children[1]==:-@)
      results = []
      exp,op = *code
      #paths = symbolic_exec(state.clone,pathcond.clone,exp,klass)
      paths = symbolic_exec state,pathcond,exp,klass
      paths.each {|st,pc| #st[:ret] = code.updated(nil, [st[:ret], op])
        st = st.merge({:ret => code.updated(nil, [st[:ret],op])})
        results.push([st,pc])
      }
      return results
    elsif (code.type==:send) & (code.children[1]==:+ || code.children[1]==:- || code.children[1]==:* || code.children[1]==:/) ## || code.children[1]==:-@ )
      results = []
      first_exp,op,second_exp = *code
      #first_paths = symbolic_exec(state.clone, pathcond.clone, first_exp, klass)
      first_paths = symbolic_exec state,pathcond,first_exp,klass
      ### below: first each state/pathcond generated from first_exp, generate state/pathcond for second_exp
      ### then, set :ret value in generated state to original operation, where first and second exp are replaced
      ### by their ret values from symbolic execution. return second state and pathcond.
      first_paths.each {|st1,pc1| #second_paths = symbolic_exec(st1.clone,pc1.clone,second_exp,klass)
        second_paths = symbolic_exec st1,pc1,second_exp,klass
        second_paths.each {|st2,pc2| #st2[:ret] = code.updated(nil, [st1[:ret],op,st2[:ret]])
          st2 = st2.merge({:ret => code.updated(nil,[st1[:ret],op,st2[:ret]])})
          results.push([st2,pc2])
        }
      }
      return results

    elsif (code.type==:send) & (code.children[1] == :[]=)
      ## array assignment
      #code = replace_vars(code, state, klass)
      arr,op,index,rhs = *code.children
      arr_var = arr.children[0]  ## save name of array
      arr = replace_vars(arr, state, klass) ## set arr to symarray object
      ## need to raise error if arr is not array
      #first_paths = symbolic_exec(state.clone, pathcond.clone, index, klass)
      first_paths = symbolic_exec state,pathcond,index,klass
      results = []
      # have to separately symex over array location being assigned to and val to which it is assigned
      first_paths.each {|st1,pc1| #second_paths = symbolic_exec(st1.clone,pc1.clone,rhs,klass)
        second_paths = symbolic_exec st1,pc1,rhs,klass
        second_paths.each {|st2,pc2| arr.contents = code.updated(:store,[arr.contents,st1[:ret],st2[:ret]]) 
          #st2[arr_var] = arr
          st2 = st2.merge({arr_var => arr})
          results.push([st2,pc2])
        }
      }
      return results
      
    elsif (code.type==:send) & (code.children[1]==:[]) ### for now this is just for array access. later will need to handle :[] for other classes.
      arr,op,index = *code
      arr = replace_vars(arr,state,klass)
      ## need to raise error here if arr is not array
      #paths = symbolic_exec(state.clone,pathcond.clone,index,klass)
      paths = symbolic_exec state,pathcond,index,klass
      results = []
      paths.each {|st,pc| #st[:ret] = code.updated(:select,[arr.contents,st[:ret]])
        st = st.merge({:ret => code.updated(:select,[arr.contents,st[:ret]])})
        results.push([st,pc])
      }
      return results

    elsif code.type==:select
      #state[:ret] = code
      state = state.merge({:ret => code})
      return [[state,pathcond]]

    elsif code.type==:send
      ### method call
      receiver,meth_name,*local_args = *code
      receiver = replace_vars(receiver,state,klass)
      real_args = []
      local_args.each_with_index {|a,i| real_args[i] = replace_vars(a,state,klass) }
                     
      if (receiver==nil) || receiver.is_a?(RDL::SymbolicObject)
        ## instance method call
        if receiver.is_a?(RDL::SymbolicObject)
          ### receiver is an object instance
          rec_class = receiver.klass
          ast = get_ast(rec_class, meth_name, true)
                     
          name, args, body = *ast
          argsHash = {}
          #args.children.each { |a| argsHash[a.children[0]] = RDL::SymbolicValue.new(a.children[0]) }
          args.children.each_with_index { |a,i| argsHash[a.children[0]] = real_args[i] } 
          argsHash[:ret] = nil
          objHash = argsHash.merge(receiver.state)
          paths = symbolic_exec(objHash, [Parser::CurrentRuby.parse("true")], body, receiver.klass)
          ### the code below exists to update the state of the symbolic object in question
          ### have to create new obj for each path
          ### however, not sure if this handles mutations correctly. similar problem with arrays. need to check on this.
          result = []
          paths.each { |st,pc| new_obj = RDL::SymbolicObject.new(remove_lvars(st),rec_class)
            res_state = state.merge({:ret => st[:ret]})
            res_state = res_state.each { |var,val| res_state[var] = replace_obj(receiver,new_obj,val) }
            res_path = pathcond+pc
            result << [res_state,res_path]
          }
          return result
          #result = []
          #paths.each { |st, p| res_state = state.clone 
          #  res_path = pathcond.clone 
          #  argsHash.each_with_index { |a,i| st.each {|var, val| st[var] = replace_symval(a[1],real_args[i],val) }
          #    p = replace_path_symvals(a[1], real_args[i],p)
          #  } 
          #  res_state[:ret] = st[:ret] 
          #  res_path = res_path.concat(p) 
          #  new_obj = RDL::SymbolicObject.new(remove_lvars(st), rec_class)
          #  res_state = res_state.each {|var, val| res_state[var] = replace_obj(receiver, new_obj, val) }
          #  result << [res_state,res_path]
          #}          
          #return result          
        end
                     
        ### receiver is nil, instance method should be in same klass as self
        klass = Object.const_get(klass) if klass.is_a?(String)
        ast = get_ast(klass, meth_name, true)
        
        name, args, body = *ast
        argsHash = {}
        #args.children.each { |a| argsHash[a.children[0]] = RDL::SymbolicValue.new(a.children[0]) }
        args.children.each_with_index { |a,i| argsHash[a.children[0]] = real_args[i] }
        argsHash[:ret] = nil
        paths = symbolic_exec(argsHash, [Parser::CurrentRuby.parse("true")], body, klass.instance_method(meth_name).owner)
        result = []
        paths.each { |st,pc| res_state = state.merge({:ret => st[:ret]})
          res_path = pathcond+pc
          result << [res_state,res_path]
        }
        return result
        #result = []
        #paths.each { |st, p| res_state = state.clone 
        #  res_path = pathcond.clone 
        #  argsHash.each_with_index { |a,i| st[:ret] = replace_symval(a[1],real_args[i],st[:ret])
        #    p = replace_path_symvals(a[1], real_args[i],p)
        #  } 
        #  res_state[:ret] = st[:ret] 
        #  res_path = res_path.concat(p) 
        #  result << [res_state,res_path]
        #}  
        #return result

      elsif (receiver.type == :const)
        ## class method call

        if meth_name==:new
          meth_class = Object.const_get(resolve_class(receiver))
          if meth_class.private_instance_methods(false).include?(:initialize) #### may need to change false to true here when considering inheritance
            ast = get_ast(meth_class, :initialize, true)
            
            name,args,body = *ast
            argsHash = {}
            #args.children.each { |a| argsHash[a.children[0]] = RDL::SymbolicValue.new(a.children[0]) }
            args.children.each_with_index { |a,i| argsHash[a.children[0]] = real_args[i] }
            argsHash[:ret] = nil
            paths = symbolic_exec(argsHash, [Parser::CurrentRuby.parse("true")], body, meth_class)
            result = []
            paths.each { |st,pc| res_state = state.merge({:ret => RDL::SymbolicObject.new(remove_lvars(st),meth_class) })
              res_path = pathcond+pc
              result << [res_state,res_path]
            }
            return result
            #result = []
            #paths.each { |st, p| res_state = state.clone 
            #  res_path = pathcond.clone 
            #  st = remove_lvars(st)
            #  argsHash.each_with_index { |a,i| st.each { |var,val| st[var] = replace_symval(a[1],real_args[i],val) }
            #    p = replace_path_symvals(a[1], real_args[i],p)
            #  } 
            #  res_state[:ret] = RDL::SymbolicObject.new(st.clone, meth_class) 
            #  res_path = res_path.concat(p) 
            #  result << [res_state,res_path]
            #}
            #return result
          else
            #state[:ret] = RDL::SymbolicObject.new({}, meth_class)
            state = state.merge({:ret => RDL::SymbolicObject.new({},meth_class)})
            return [[state, pathcond]]
          end
        end

        meth_class = Object.const_get(resolve_class(receiver))
        ast = get_ast(meth_class, meth_name, false)
        
        _,name,args,body = *ast
        argsHash = {}
        #args.children.each { |a| argsHash[a.children[0]] = RDL::SymbolicValue.new(a.children[0]) }
        args.children.each_with_index { |a,i| argsHash[a.children[0]] = real_args[i] }
        argsHash[:ret] = nil
        
        paths = symbolic_exec(argsHash, [Parser::CurrentRuby.parse("true")], body, meth_class)
        result = []
        paths.each { |st,pc| res_state = state.merge({:ret => st[:ret]})
          res_path = pathcond+pc
          result << [res_state,res_path]
        }
        return result
        #result = []
        #paths.each { |st, p| res_state = state.clone 
        #  res_path = pathcond.clone 
        #  argsHash.each_with_index { |a,i| st[:ret] = replace_symval(a[1],real_args[i],st[:ret])
        #    p = replace_path_symvals(a[1], real_args[i],p)
        #  }
        #  res_state[:ret] = st[:ret] 
        #  res_path = res_path.concat(p) 
        #  result << [res_state,res_path]
        #}

        #return result
      else
        #### should be case that receiver is symbolic
        puts "error here"
      end
                     
    end
  end
  
  def self.remove_lvars(state)
    state = state.clone
    state.delete_if { |var,val| !var.to_s.include?("@") }
    return state
  end
  
  def self.resolve_class(ast)
    if ast==nil
      return ast
    elsif !ast.respond_to?(:children)
      return ast
    elsif ast.type == :const
      scope = resolve_class(ast.children[0])
      klass = resolve_class(ast.children[1])
      return scope+"::"+klass if scope
      return klass
    elsif ast.type == :lvar
      return ast.children[0].to_s
    end
  end
  
  def self.replace_obj(old, new, exp)
    if exp == old
      return new
    elsif !exp.is_a?(Parser::AST::Node)
      return exp
    elsif exp.respond_to?(:children)
      return exp.updated(nil, exp.children.map { |c| replace_obj(old,new, c) })
    else return exp
    end
  end


  # replace var with name and value in expression exp
  def self.replace_exp(name, value, exp)
    if !exp.is_a?(Parser::AST::Node)
      return exp
    elsif exp.type == :send && exp.children[0] == nil
      return value if exp.children[1] == name ## still needed here?
    elsif exp.type == :lvar
      return value if exp.children[0] == name
      ## need case for ivars if going to use here
    elsif exp.respond_to?(:children)
      return exp.updated(nil, exp.children.map { |c| replace_exp(name, value, c) })
    else return exp
    end
  end

  def self.replace_symval(symval, val, exp)
    if exp.is_a?(RDL::SymbolicValue)
      return val if exp == symval
      return exp
    elsif !exp.is_a?(Parser::AST::Node) || !exp.respond_to?(:children)
      return exp
    else
      return exp.updated(nil, exp.children.map {|c| replace_symval(symval, val, c) })
    end
  end

  def self.replace_path_symvals(symval, val, path)
    path = path.clone
    path.map {|c| replace_symval(symval, val, c)}
  end
      

  # replace var with name and value in path condition
  def self.replace_path(name, value, pathconds)
    pathconds = pathconds.map
    pathconds.map { |c| replace_exp(name, value, c) }
  end

  def self.replace_vars(exp, state, klass)
    if !exp.is_a?(Parser::AST::Node) || !exp.respond_to?(:children)
      return exp
    elsif exp.type == :lvar
      return state[exp.children[0]]
      ## error here if var not found in state
    elsif exp.type == :ivar
      var = exp.children[0]
      if state.include?(var)
        return state[var]
      else
        klass = Object.const_get(klass) if klass.is_a?(String)
        return Parser::CurrentRuby.parse(klass.instance_variable_get(var).to_s)
      end
      return state[exp.children[0]] if state.include?(exp.children[0])
      #### error here if var not found
    else
      return exp.updated(nil, exp.children.map { |c| replace_vars(c, state, klass) })
    end
  end

  def self.get_ast(klass, meth, inst)
    #file, line = $__rdl_info.get(klass, meth, :source_location)
    if inst
      "here1 and klass: #{klass} and meth: #{meth}"
      file, line = klass.instance_method(meth.to_sym).source_location
    else
      "here2 and klass: #{klass} and meth #{meth}"
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
    cache_hit = (($__rdl_ruby_parser_cache.has_key? file) &&
                 ($__rdl_ruby_parser_cache[file][0] == digest))
    unless cache_hit
      file_ast = Parser::CurrentRuby.parse_file file
      mapper = ASTMapper.new(file)
      mapper.process(file_ast)
      cache = {ast: file_ast, line_defs: mapper.line_defs}
      $__rdl_ruby_parser_cache[file] = [digest, cache]
    end
    ast = $__rdl_ruby_parser_cache[file][1][:line_defs][line]
    raise RuntimeError, "Can't find source for class #{RDL::Util.pp_klass_method(klass, meth)}" if ast.nil?
    return ast
  end
    
end
  


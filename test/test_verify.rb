require 'minitest/autorun'
$LOAD_PATH << File.dirname(__FILE__) + "/../lib"
require 'rdl'
require 'types/core'

class D ; end
module M ; end
class F ; end
class G ; end
class X ; end
class Y ; end
class Z ; end
class VerifyErr ; end

class TestVerify < Minitest::Test

  def setup
    RDL::Verify.set_testing(true)
    RDL::Verify.set_use_assume(false)
  end
  
  def do_translate(klass, meth, block_name="block")
    #if meth starts with "self." then it is singleton meth
    klass = klass.to_s
    inst = true
    if meth.is_a?(String) && meth =~ /^self\./
      inst = false
      meth = $'
    end
    added = []
    meths_res = RDL::Verify.get_translated_meths([[klass, meth, inst]], added)
    struct = "(struct object ([classid][objectid] "
    fields_added = ["classid"]
    RDL.translate_fields.each_key { |kl|
      RDL.translate_fields[kl].each_key { |instvar| struct << "[#{instvar} #:auto #:mutable] " unless fields_added.include? instvar.to_s
        fields_added << instvar.to_s }} 
    struct << "))\n"
    ret = struct
    meths_res.each { |r| ret = ret+r }
    ret
  end

  def do_translate_literal(lit)
    ast = Parser::CurrentRuby.parse lit
    RDL::Verify.translate(ast, nil, nil, nil, nil, nil, false)[0]
  end

  def obj_to_int(str)
    if RDL::Verify::USE_BV then "(bitvector->integer (object-value #{str}))" else "(object-value #{str})" end
  end

  def assert_verified(code)
    assert_equal "(unsat)", RDL::CLine.call(code).chomp
  end


  def test_def
    self.class.class_eval {
      type '(Fixnum) -> Fixnum'
      def def_identity(x) x; end
    }
    racket1 = do_translate(self.class, :def_identity)+"(#{self.class}_inst_def_identity (void) 4)"
    assert_equal def_identity(4), RDL::CLine.call(racket1, true).to_i

    self.class.class_eval {
      type '(%bool, %bool) -> %bool'
      def def_and(a, b) a && b; end
    }
    racket3 = do_translate(self.class, :def_and)+"(#{self.class}_inst_def_and (void) true false)"
    assert_equal "#f", RDL::CLine.call(racket3, true).chomp!

    self.class.class_eval {
      type '(Fixnum, Fixnum) -> %integer'
      def def_add(x, y) x+y; end
    }
    racket4 = do_translate(self.class, :def_add)+obj_to_int("(#{self.class}_inst_def_add (void) (int 4) (int 4))")
    
    assert_equal def_add(4, 4), RDL::CLine.call(racket4, true).to_i

    self.class.class_eval {
      type '(%integer x) -> %integer res {{ res == x }}', verify: :now
      def def_verify_identity(x)
        x
      end
    }

    self.class.class_eval {
      type '(Fixnum x) -> %integer y {{ y == x+1 }}', verify: :now
      def def_plus_one(x) x+1; end
    }

    self.class.class_eval {
      def def_plus_one_wrong(x) x+2; end
    }
    assert_raises(RDL::Verify::VerifyError) {
      type self.class, :def_plus_one_wrong, '(Fixnum x) -> %integer y {{ y == x+1 }}', verify: :now
    }
    
  end

  def test_defs
    self.class.class_eval {
      type '(Fixnum) -> Fixnum'
      def self.def_identity(x) x; end
    }
    racket1 = do_translate(self.class, "self.def_identity")+"(#{self.class}_def_identity (void) 42)"
    assert_equal self.class.def_identity(42), RDL::CLine.call(racket1, true).to_i

    self.class.class_eval {
      type '(%bool, %bool) -> %bool'
      def self.def_and(a, b) a && b; end
    }
    racket3 = do_translate(self.class, "self.def_and")+"(#{self.class}_def_and (void) true false)"
    assert_equal "#f", RDL::CLine.call(racket3, true).chomp!

    self.class.class_eval {
      type '(Fixnum, Fixnum) -> %integer'
      def self.def_add(x, y) x+y; end
    }
    racket4 = do_translate(self.class, "self.def_add")+obj_to_int("(#{self.class}_def_add (void) (int 4) (int 4))")
    assert_equal self.class.def_add(4, 4), RDL::CLine.call(racket4, true).to_i

    self.class.class_eval {
      type '(%integer x) -> %integer res {{ res == x }}', verify: :now
      def self.defs_verify_identity(x)
        x
      end
    }
    
    self.class.class_eval {
      type '(Fixnum x) -> %integer y {{ y == x+1 }}', verify: :now
      def self.defs_plus_one(x) x+1; end
    }

    self.class.class_eval {
      def self.defs_plus_one_wrong(x) x+2; end
    }
    assert_raises(RDL::Verify::VerifyError) {
      type self.class, 'self.defs_plus_one_wrong', '(Fixnum x) -> %integer y {{ y == x+1 }}', verify: :now
    }
  end

  def test_singleton_method_const
    X.class_eval {
      type '(Fixnum) -> Fixnum'
      def foover(x) x; end
      
      type '(Fixnum) -> Fixnum'
      def self.barver(x) x; end
    }

    Y.class_eval {
      type '(Fixnum) -> Fixnum'
      def self.barver(x) X.barver(x); end
      
      type '(Fixnum) -> Fixnum'
      def self.foover(x) a = X.new; a.foover(x); end      
    }

    racket1 = do_translate(Y, "self.barver")+"(Y_barver (void) 42)"
    assert_equal Y.barver(42), RDL::CLine.call(racket1, true).to_i

    racket2 = do_translate(Y, "self.foover")+"(Y_foover (void) 42)"
    assert_equal Y.foover(42), RDL::CLine.call(racket2, true).to_i
  end

  def test_instance_method

    X.class_eval {
      type '(Fixnum) -> Fixnum'
      def inst_meth_caller(x)
        inst_meth_callee(x)
      end

      type '(Fixnum) -> Fixnum'
      def inst_meth_callee(x)
        x
      end
    }

    racket1 = do_translate(X, "inst_meth_caller")+"(X_inst_inst_meth_caller (void) 42)"
    tmp = X.new
    assert_equal tmp.inst_meth_caller(42), RDL::CLine.call(racket1, true).to_i
  end

  def test_array_basics
    X.class_eval {
      type '(%integer) -> Array<%integer>'
      def to_a(x)
        [x]
      end
    }

    racket1 = do_translate(X, "to_a")
    tmp = X.new

    # Assert that size of the array is 1

    assert_equal tmp.to_a(22).size, RDL::CLine.call(
                   racket1 + obj_to_int("(Array_inst_size (X_inst_to_a (void) 22))"), true).to_i
    # Assert that the array contains 22
    assert_equal "#t", RDL::CLine.call(
                   racket1 + "(Array_inst_include? (X_inst_to_a (void) 22) 22)", true).chomp
    assert_equal "#f", RDL::CLine.call(
                   racket1 + "(Array_inst_include? (X_inst_to_a (void) 22) 27)", true).chomp
  end

  def test_array_constructors
    X.class_eval {
      type '() -> Array'
      def get_array
        Array.new
      end

      type '(%integer) -> Array'
      def get_sized_array(s)
        Array.new(s)
      end

      type '(%integer, %integer) -> Array'
      def get_filled_array(s, f)
        Array.new(s, f)
      end
    }

    racket1 = do_translate(X, "get_array")
    racket2 = do_translate(X, "get_sized_array")
    racket3 = do_translate(X, "get_filled_array")

    # Does a new array (0 arg constructor) have size 0?
    assert_equal 0, RDL::CLine.call(racket1 + "(Array_inst_size (X_inst_get_array (void)))").to_i

    # For a generic size array, are all elements nil for a generic in-bounds index?
    assert_verified(racket2 +
                    "(define size (new-symbolic-size))" +
                    "(define idx (new-symbolic-index (prim_int size)))" +
                    "(define a (X_inst_get_sized_array (void) size))" +
                    "(verify (assert (and (Integer_inst_== (Array_inst_size a) size) (eq? nil (Array_inst_ref a idx)))))")

    # For a generic size array with a defined fill, do all elements get set to that index?
    assert_verified(racket3 +
                    "(define size (new-symbolic-size))" +
                    "(define idx (new-symbolic-index (prim_int size)))" +
                    "(define a (X_inst_get_filled_array (void) size (int 1)))" +
                    "(verify (assert (and (Integer_inst_== (Array_inst_size a) size) (Integer_inst_== (int 1) (Array_inst_ref a idx)))))")

  end

  def test_array_assignments
    X.class_eval {
      type '(%integer, %integer) -> %integer'
      def set_two_indices(i1, i2)
        a = Array.new
        v = 4
        a[i1] = v
        a[i2] = v

        return a.size
      end

      type '(%integer, %integer) -> %integer'
      def int_max(x, y)
        if x>y then x else y end
      end
    }

    racket = do_translate(X, "set_two_indices") 

    # Assert that when two indices are set in an empty array, the size of the array is always one more than the largest affected index
    # This tests the resizing of arrays

    assert_verified(racket +
                    "(let ([ti1 (new-symbolic-index array-capacity)][ti2 (new-symbolic-index array-capacity)])
                    (verify (assert (Integer_inst_== (X_inst_set_two_indices (void) ti1 ti2) (Integer_inst_+ (if (Integer_inst_> ti1 ti2) ti1 ti2) (int 1))))))")

  end

  def test_array_deletion
    X.class_eval {
      type '(%integer, %integer, %integer) -> Array'
      def delete_three(i, j, k)
        a = Array.new 10
        a.delete_at i
        a.delete_at j
        a.delete_at k
        return a
      end
    }

    racket = do_translate(X, "delete_three")

    # Deletion of any three indices should result in an array containing 7 things, all nil

    assert_verified(racket +
                    "(let* ([ti1 (new-symbolic-index 10)][ti2 (new-symbolic-index 9)][ti3 (new-symbolic-index 8)][ti4 (new-symbolic-index 7)][res (X_inst_delete_three (void) ti1 ti2 ti3)])
                    (verify (assert (and (Integer_inst_== (int 7) (Array_inst_size res)) (equal? (Array_inst_ref res ti4) nil)))))")

  end

  def test_lits
    assert_equal "(void)", do_translate_literal("nil")
    assert_equal "false", do_translate_literal("false")
    assert_equal "true", do_translate_literal("true")
  end


  def test_verified_meths
    self.class.class_eval{
      type '(%integer x) -> %integer ret {{ ret == x || ret == -x }}', verify: :now
      def abs(x)
        if x<0
          -x
        else
          x
        end
      end
    }

  X.class_eval {
    type '(Fixnum) -> Fixnum'
    def self.foo(x)
      x
    end
  }
  Y.class_eval {    
    type '(Fixnum x) -> Fixnum y {{ x == y }}', verify: :now
    def bar(x)
      X.foo(x)
    end
  }

  F.class_eval {
    type '(Fixnum x {{ x > 5 && x < 10}}, Fixnum y {{ y > 5 && y < 10 }}) -> %integer z {{ z > 10 && z < 20}}', verify: :now
    def bar(x, y)
      x+y
    end
  }

  G.class_eval { 
    type '(%integer x) -> %integer z {{ z == 1 || z == 0 }}', verify: :now
    def foo(x)
      x % 2
    end
  }

  VerifyErr.class_eval {
    type '() -> %integer result {{ result.exception? }}', verify: :now
    def returns_error
      raise
    end

    type '(%bool b) -> %integer result {{ result.exception? || result + 1 == 2 }}', verify: :now
    def returns_error_or_one(b)
      if b
        1
      else
        raise
      end
    end
  }

  D.class_eval {    
    var_type :@in, '%integer'

    type '(%integer) -> self'
    def initialize(x)
      @in = x
    end

    type '() -> %integer'
    def abs_in
      if @in > 0
        @in = @in
      else
        @in = -@in
      end
    end

    type '() -> %integer'
    def give_in
      @in
    end
  }



  
  M.class_eval {
    type :modifyIn, '(D d) -> Fixnum', modifies: {:d => [:@in]}, modular: true, pure: true
    type :add_one, '(%integer x) -> %integer y {{ y == x+1 }}', modular: true, pure: true, verify: :now

    type '(%integer x {{ x > -32 }}) -> %integer y {{ y >= 0 }}', verify: :now
    def bar(x)
      d = D.new(x)
      d.abs_in
      d.give_in
    end
    
    def foo(y)
      d = D.new(y)
      d.abs_in
      modifyIn(d)
      d.give_in
    end

    type '(%integer x) -> %integer y {{ y == x+1 }}', verify: :now
    def baz(x)
      add_one(x)
    end
  }

  assert_raises(RDL::Verify::VerifyError) {
    M.class_eval {
      type :foo, '(%integer y) -> %integer res {{ y >=0 }}', verify: :now
    }
  }

  Z.class_eval {
    def add_one(x)
      x+2
    end
  }
  assert_raises(RDL::Verify::VerifyError) {
    Z.class_eval {
      include M
    }
  }
    

  
  end

  
end

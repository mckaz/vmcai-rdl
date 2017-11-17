require 'rdl'
require 'types/core'

class A

  type '(%integer) -> %integer'
  def abs(x)
    if x<0
      -x
    else
      x
    end
  end

  assert(A, :abs) { |x, ret| ret == x || ret == -x }

end

class X
  type '(Fixnum) -> Fixnum'
  def self.foo(x)
    x
  end
end

class Y
  
  type '(Fixnum x) -> Fixnum y {{ x == y }}', verify: :now
  def bar(x)
    X.foo(x)
  end
  
end

class F

  type '(Fixnum x {{ x>0 }}) -> Fixnum y {{ y > 0 }}', verify: :now
  def foo(x)
    x
  end

  type '(Fixnum x {{ x > 5 }}, Fixnum y {{ y > 5 }}) -> %integer z {{ z > 10 }}', verify: :now
  def bar(x, y)
    x+y
  end
end

class G

  type '(%integer x) -> %integer z {{ z == 1 || z == 0 }}', verify: :now
  def foo(x)
    x % 2
  end
  
end

class D
  
  var_type :@in, '%integer'

  type '(%integer) -> self'
  def initialize(x)
    @in = x
  end

  type '() -> %integer'
  def abs_in
    if @in > 0
      @in
    else
      -@in
    end
  end
end


class E

  type '(%integer x) -> %integer y {{ y >= 0 }}', verify: :now
  def foo(y)
    a = nil
    d = D.new(y)
    d.abs_in
  end

end

class Z
  type '(Fixnum x) -> Fixnum y {{ x == y}}', verify: :now
  def foo(x)
    hsh = {1 => x, "2" => 3}
    y = -1
    hsh.each { |k, v| if v == x then y = x end }
    y
  end

end


class B

  type '(%integer) -> %integer'
  def plus_one(x)
    apply_block(x) { |num| num+1 }
  end

  type '(%integer) { (%integer) -> %integer } -> %integer'
  def apply_block(x)#, &blk)
    yield x
  end

  assert(B, :plus_one) { |x, ret| ret == x+1 }
  
end

class One
  type '() -> Fixnum'
  def bar
    1
  end
end

class Two
  type '() -> Fixnum'
  def bar
    2
  end
end

class MethDispatch

  type '(Fixnum x {{ x == 2 }} ) -> Fixnum y {{ y == 1}}', verify: :now
  def foo(x)
    if x == 1
      a = One.new
    else
      a = Two.new
    end
    a.bar
  end
end


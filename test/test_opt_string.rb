# type checking optional arguments

require 'rdl'
require 'types/core'

class TestOptString
	type 'foo', '(String, ?String) -> String', typecheck: :now
	def foo (x, f='x')
		x 
	end

	type 'bar', '(String) -> String', typecheck: :now
	def bar(x) 
		foo(x) # {|y| y}
	end	
end

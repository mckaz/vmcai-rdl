# type checking optional blocks

require 'rdl'
require 'types/core'

class TestOptBlock
	type 'opt_block', '(String) ?{(String) -> String} -> String', typecheck: :now
	def opt_block (x, &f)
	 	x 
	end

	type 'pass_opt_block', '(String) ?{(String) -> String}  -> String', typecheck: :now
	def pass_opt_block (x, &f)
	 	opt_block(x, &f) 
	end

	type 'pass_block', '(String) {(String) -> String}  -> String', typecheck: :now
	def pass_block (x, &f)
	 	opt_block(x, &f) 
	end

	type 'call_block', '(String) -> String', typecheck: :now
	def call_block (x)
	 	opt_block(x) {|y| y} 
	end

	type 'no_block', '(String) -> String', typecheck: :now
	def no_block (x)
	 	opt_block(x) 
	end

end

class TestBlock

	type 'def_block', '(String, String) {(String) -> String} -> String', typecheck: :now
	def def_block (x, y, &f)
		x 
	end

	type 'pass_block', '(String, String) {(String) -> String} -> String', typecheck: :now
	def pass_block (x, y, &f)
		def_block(x,y, &f)
		x 
	end

	type 'call_block', '(String, String) {(String) -> String} -> String', typecheck: :now
	def call_block (x, y, &f)
		def_block(x,y) {|x| x}
		x 
	end

	type 'no_block_error', '(String) -> String' # , typecheck: :now # bar should not type check
	def no_block_error(x) 
		def_block(x, x) 
	end	
end


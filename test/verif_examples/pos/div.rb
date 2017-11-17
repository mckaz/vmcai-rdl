require "rdl"
require "types/core"

type '(%integer x, %integer y {{ not (y == 0)}}) -> %integer z {{ z  = x / y }}', verify: :now
def div(x, y)
	x / y 
end


# This should be unsafe
def bad_div ()
	div(42, 0) 
end


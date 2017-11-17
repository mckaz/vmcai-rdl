require "rdl"
require "types/core"

type '(%integer x, %integer y {{ y != 0 }}) -> %integer z {{ z  = x / y }}', verify: :now
def div(x, y)
	x / y 
end
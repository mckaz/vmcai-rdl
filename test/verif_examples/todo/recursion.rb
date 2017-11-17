require "rdl"
require "types/core"

type '(%integer x) -> %integer y {{ false }}' , verify: :now
def rec(x)
	rec(x)
end
module RDL::SMT

  class SMT
  end

  class Bool < SMT
    attr_reader :value

    def initialize(value)
      @value = value
    end

    def to_s
      return "Bool(value.to_s)"
    end
  end

  class Int < SMT
    attr_reader :value

    def initialize(value)
      @value = value
    end

    def to_s
      return "Int(#{value.to_s})"
    end
  end
  
  class And < SMT
    attr_reader :first
    attr_reader :second

    def initialize(first, second)
      @first = first
      @second = second
    end

    def to_s
      return "And(#{@first.to_s}, #{@second.to_s})"
    end
  end

  class Or < SMT
    attr_reader :first
    attr_reader :second

    def initialize(first, second)
      @first = first
      @second = second
    end

    def to_s
      return "Or(#{@first.to_s}, #{@second.to_s})"
    end
  end

  

end

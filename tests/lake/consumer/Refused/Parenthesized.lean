module

public import CAS.IncludeStr

/-! A path in parentheses, which the check refuses. -/

/-- A path in parentheses is not a plain literal. -/
public def parenthesized : String := include_str ("data.txt")

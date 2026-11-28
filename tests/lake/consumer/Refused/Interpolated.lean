module

public import CAS.IncludeStr

/-! An interpolated string as the path, which the check refuses. -/

/-- An interpolated string is not a plain literal. -/
public def interpolated : String := include_str s!"data.txt"

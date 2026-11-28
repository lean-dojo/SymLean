module

public import CAS.IncludeStr

/-! A path joined from two parts, which the check refuses. -/

/-- Lean's own spelling of a path in parts, which is not one literal. -/
public def joined : String := include_str "." / "data.txt"

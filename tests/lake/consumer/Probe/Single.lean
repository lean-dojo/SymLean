module

public import CAS.IncludeStr

/-! A probe whose path stands on the line of the keyword. -/

/-- The text of `single.txt`, embedded on one line. -/
public def single : String := include_str "single.txt"

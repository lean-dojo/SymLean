module

public import CAS.IncludeStr

/-! A probe whose path stands on the line after the keyword. -/

/-- The text of `multi.txt`, its path on the next line after a comment. -/
public def multi : String := include_str -- the file next to this module
  "multi.txt"

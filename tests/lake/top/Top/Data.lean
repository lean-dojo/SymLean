module

public import CAS.IncludeStr

/-! The embedded text of the package two levels above SymLean. -/

/-- The text of `top.txt`, which `run.sh` writes. -/
public def topData : String := include_str "top.txt"

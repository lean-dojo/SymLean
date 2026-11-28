module

public import CAS.IncludeStr

/-! A notation defined and used in one module, which the check refuses at the use. -/

/-- A notation that expands to `include_str`, refused at its use. -/
notation "embed! " path => include_str path

public def notationUse : String := embed! "data.txt"

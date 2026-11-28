module

public import CAS.IncludeStr

/-! A macro defined and used in one module, which the check refuses at the use. -/

/-- A macro that expands to `include_str`, refused at its use. -/
macro "embed! " path:str : term => `(include_str $path)

public def macroUse : String := embed! "data.txt"

module

import Refused.MacroDef

/-! A use of the macro of `Refused.MacroDef`, which the check refuses. -/

/-- The macro of `Refused.MacroDef`, refused at this use by the check that it passes on. -/
public def macroTwo : String := embedTwo! "data.txt"

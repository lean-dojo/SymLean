module

import Refused.ElabDef

/-! A use of the elaborator of `Refused.ElabDef`, which the check refuses. -/

/-- The elaborator of `Refused.ElabDef`, refused at this use. -/
public def elabTwo : String := embedThree! "data.txt"

module

import Refused.NotationDef

/-! A use of the notation of `Refused.NotationDef`, which the check refuses. -/

/-- The notation of `Refused.NotationDef`, refused at this use. -/
public def notationTwo : String := embedNote! "data.txt"

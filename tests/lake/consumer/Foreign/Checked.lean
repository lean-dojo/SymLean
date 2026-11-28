module

import Macros.Embed
import CAS.IncludeStr

/-! Another library's macro, used in a module that loads the check, which refuses the use. -/

/-- The same macro in a module that loads the check, which refuses it at the use. -/
public def foreignChecked : String := embedForeign! "data.txt"

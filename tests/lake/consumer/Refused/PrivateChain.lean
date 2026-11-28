module

import Refused.Private

/-! A module whose only route to the check is the private import of `CAS.IncludeStr` in
`Refused.Private`, which Lean does not follow, so the facet refuses it. -/

/-- The check of `Refused.Private` is not loaded here: Lean does not follow its private import. -/
public def privateChain : String := include_str "data.txt"

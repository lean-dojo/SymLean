/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Expr.Syntax

/-!
# Missing facts for certified evaluation

`RegistryRequirements` lists what a rational-interval registry lacks to evaluate an expression:
the denominators that it cannot prove nonzero on its chart. Requirements are computable planner
data, not certificates. They affect evaluation only after a solver turns them into checked
registry entries. Unary operations need no entry, because FloatLib computes their ranges from the
interval of the argument.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

/-- Facts a certified evaluator is missing for a given expression.

These requirements are computed with the evaluation context that later evaluates the
expression. They are proof-search targets rather than certificates; a fact affects trusted
evaluation only after it has been turned into a checked registry entry. -/
structure RegistryRequirements (ι : Type*) where
  /-- Denominators with neither a registered lower bound on their absolute value nor an
  enclosure that excludes zero. -/
  missingDenominators : List (Verified.Expr ι)

namespace RegistryRequirements

/-- An empty set of registry requirements. -/
def empty {ι : Type*} : RegistryRequirements ι where
  missingDenominators := []

/-- Combine two sets of registry requirements. -/
def append {ι : Type*} (a b : RegistryRequirements ι) : RegistryRequirements ι where
  missingDenominators := a.missingDenominators ++ b.missingDenominators

end RegistryRequirements

end RationalInterval
end CAS.Continuum

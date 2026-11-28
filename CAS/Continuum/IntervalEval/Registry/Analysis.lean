/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalEval.Planning.Requirements
public import CAS.Continuum.IntervalEval.Registry.Core

/-!
# Facts an interval registry is missing for an expression

`CertifiedEvalRegistry.requirements` scans an expression and returns its `RegistryRequirements`
for one registry: the denominators that the registry's context cannot prove nonzero on the chart,
each of which needs an absolute lower bound (`denominatorRequirement`). The result is planner
data. It affects evaluation only after a solver turns it into checked registry entries.

## Implementation notes

`requirements` is a structural recursion over the expression. At a quotient `a / b` it asks the
context of the registry whether `b` is nonzero on the chart
(`CertifiedEvalContext.certifiesNonzero`): by a registered lower bound on `|b|`, or by an
enclosure of `b` that excludes zero, which FloatLib computes with the facts the registry already
holds. Only a denominator that passes neither test is missing. No other operation needs a
registry fact, since FloatLib computes the ranges of the unary operations and of the real power
from the intervals of their arguments. The scan proves nothing and needs no theorem. Its caller
`extendWithSolvedDenominatorsOfSimplified?` (`CAS.Continuum.IntervalEval.Registry.Refinement`)
turns the list into entries that carry their own proofs, and like the rest of the planner it
runs in the kernel when a CEGA query is reduced.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open CAS.Verified

namespace CertifiedEvalRegistry

variable {α : Type*} {ι : Type*} [DecidableEq ι] {s : Set α} {ρ : α → ι → ℝ}

/-- Requirements contributed by one denominator: none when the registry's context proves it
nonzero on the chart, and the denominator itself otherwise. -/
def denominatorRequirement (r : CertifiedEvalRegistry s ρ) (den : Verified.Expr ι) :
    RegistryRequirements ι :=
  if r.toContext.certifiesNonzero den then .empty else { missingDenominators := [den] }

/-- Scan an expression for the denominator facts missing from this registry. -/
def requirements (r : CertifiedEvalRegistry s ρ) :
    Verified.Expr ι → RegistryRequirements ι
  | .nat _ | .int _ | .rat _ _ | .pi | .e | .var _ =>
      RegistryRequirements.empty
  | .add a b | .mul a b | .sub a b | .rpow a b =>
      (requirements r a).append (requirements r b)
  | .div a b =>
      ((requirements r a).append (requirements r b)).append (r.denominatorRequirement b)
  | .neg a | .pow a _ | .sin a | .cos a | .atan a | .asin a | .acos a | .exp a | .log a |
      .sqrt a =>
      requirements r a

end CertifiedEvalRegistry
end RationalInterval
end CAS.Continuum

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalEval.Registry.Analysis
public import CAS.Continuum.IntervalEval.Registry.Denominator

/-!
# Extending registries and scoring subdivision coordinates

`extendWithEasyFacts?` simplifies an expression and adds to a registry the denominator lower
bounds it needs (`extendWithSolvedDenominatorsOfSimplified?`). `extendWithDenominatorFactsFor?`
certifies an explicit list of nonzero side conditions. `variableSensitivity?` and
`variableSensitivities` score a coordinate `i` for subdivision by its interval width times
`absMax` of the enclosure of `∂ᵢ f` on the chart.

## Implementation notes

The passes only propose entries; each entry carries its own soundness proof, and a pass that
cannot solve every missing denominator returns `none` rather than a partial registry. One pass is
enough, because the denominators are the only facts a registry stores: FloatLib computes the
ranges of the unary operations from the intervals of their arguments when the context evaluates
the expression.

The sensitivity score is ours and plays no part in soundness. By the mean value theorem,
`width(Bᵢ) · max |Dᵢ|`, with `Dᵢ` an enclosure of `∂ᵢ f` on the chart, bounds how much `f` can
vary along coordinate `i`, so the planner bisects where this first-order bound is largest.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open CAS.Verified

namespace CertifiedEvalRegistry

variable {α : Type*} {ι : Type*} [DecidableEq ι] {s : Set α} {ρ : α → ι → ℝ}

/--
Try to extend a registry with denominator facts for an explicit side-condition frontier.

A symbolic route such as `(x / y) * y = x` already knows that it needs `y ≠ 0`,
even when the interval evaluator has not generated that requirement. CEGA can
therefore ask the chart solver to certify precisely the route's required
nonzero expressions and then reuse the exact route proof.
-/
def extendWithDenominatorFactsFor?
    (r : CertifiedEvalRegistry s ρ) (denominators : List (Verified.Expr ι)) :
    Option (CertifiedEvalRegistry s ρ) :=
  match denominators.mapM r.denominatorRouteEntry? with
  | some [] => some r
  | some generated => some { r with divEntries := r.divEntries ++ generated }
  | none => none

/-- Solve the denominator requirements of an expression that has already been simplified. -/
def extendWithSolvedDenominatorsOfSimplified?
    (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr ι) :
    Option (CertifiedEvalRegistry s ρ) :=
  r.extendWithDenominatorFactsFor? (r.requirements expr).missingDenominators

/-- Run the easy CEGA solver on the simplified expression.

The pass adds a lower bound on the absolute value of every denominator that the registry cannot
yet prove nonzero, found by the structural solver `denominatorRouteEntry?` from registered
facts, variable intervals, products and powers. It is conservative: if one denominator cannot be
solved, the whole extension fails instead of producing a partial registry.
-/
def extendWithEasyFacts?
    (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr ι) :
    Option (CertifiedEvalRegistry s ρ) :=
  r.extendWithSolvedDenominatorsOfSimplified? (Verified.Expr.simplify expr)

/-! ### Subdivision candidates -/

/-- Proof-free coordinate candidate used by the subdivision planner.

`priority` is either a first-order sensitivity score or a fallback interval
width. The source width is retained only as a deterministic tie-breaker.
The construction path determines which score was used, so no separate tag is
stored. Neither quantity participates in the soundness proof of the eventual
cover.
-/
structure VariableSubdivisionChoice (ι : Type*) where
  /-- Coordinate proposed for bisection. -/
  coordinate : ι
  /-- Planner priority: influence score or fallback interval width. -/
  priority : ℚ
  /-- Width of the source interval, used to break equal-priority ties. -/
  width : ℚ

/--
Compute one first-order variable-sensitivity score when interval evaluation
can enclose the corresponding symbolic partial derivative.

Zero-width coordinates and variables absent from the expression are
discarded because bisecting either cannot improve the enclosure.
-/
def variableSensitivity?
    (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr ι) (i : ι) :
    Option (VariableSubdivisionChoice ι) :=
  let source := r.env i
  let width := source.hi - source.lo
  if expr.containsVar i && decide (source.lo < source.hi) then
    match r.toContext.evalSimplified (expr.diff i) with
    | none => none
    | some derivativeRange =>
        some
          { coordinate := i
            priority := width * derivativeRange.absMax
            width }
  else
    none

/--
First-order sensitivity scores for the splittable variables among `coordinates`,
in the order of that list.

The caller supplies the coordinate enumeration (`List.finRange n` for `Fin n`)
instead of this function sorting `Finset.univ`: CEGA queries are evaluated by
the kernel, and `Finset.sort` reduces through `List.mergeSort`, whose body Lean
core does not expose to module files.
-/
def variableSensitivities
    (r : CertifiedEvalRegistry s ρ) (coordinates : List ι) (expr : Verified.Expr ι) :
    List (VariableSubdivisionChoice ι) :=
  coordinates.filterMap (r.variableSensitivity? expr)

end CertifiedEvalRegistry
end RationalInterval
end CAS.Continuum

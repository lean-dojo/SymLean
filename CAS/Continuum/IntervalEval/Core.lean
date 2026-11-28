/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Arithmetic
public import CAS.Continuum.IntervalEval.WellFormed
public import CAS.Expr.FloatLib
public import CAS.Route.Step
public import FloatLib.Numerics.Enclosure.Expression.BackendsProof

/-!
# FloatLib's evaluation of verified expressions

FloatLib evaluates the expressions of the interval planner. `evalWith` writes an expression of
`Verified.Expr` in FloatLib's expression language with its variables numbered by occurrence,
evaluates it with the zero rule on a FloatLib backend with rational endpoints and FloatLib's
standard calls `π`, `x ^ y` and `e`, and reads the result back as a `RationalInterval`.
`evalPolynomial` is this evaluation on FloatLib's exact backend `Backend.rational`.

The module also holds the denominator facts of the certified contexts of
`CAS.Continuum.IntervalEval.Context`: lower bounds on the absolute values of denominators,
proved on a chart and collected from finite lists of planner entries.

## Main definitions

* `floatLibEval?`, `evalWith`: FloatLib's evaluation of an expression on a backend with rational
  endpoints, and the same read back as an ordered rational interval.
* `evalPolynomial`: `evalWith` on `Backend.rational`, after the well-formedness check.
* `AbsLowerResult`, `ExprAbsLowerProvider`, `ExprAbsLowerRouteEntry`,
  `ExprAbsLowerProvider.fromRouteEntries`: checked lower bounds on the absolute values of
  denominators, assembled from finite lists of planner entries.

## Main results

* `containsReal_floatLibEval?`, `evalWith_sound`, `evalPolynomial_sound`: a successful evaluation
  contains the value of the expression at every point whose coordinates lie in their intervals.

## Implementation notes

FloatLib's result is a pair of rational endpoints. The read-back takes its order from FloatLib's
containment theorem at the lower corner of the box, the point where every variable takes the
lower end of its interval: the result contains the value of the expression there, so its lower
end is at most its upper end (`lo_le_hi_of_floatLibEval?`). No comparison is evaluated for it.

Numbering by occurrence (`Verified.Expr.numberOccurrences`) needs neither decidable equality nor
an enumeration of the labels, so `evalWith` works for labels of any type. The box repeats the
interval of a variable at each of its occurrences. An interval evaluation reads every occurrence
on its own anyway, so this gives the enclosure of numbering by label.

On literals, variables, sums, differences, products, negations and natural powers,
`evalPolynomial` is exact rational interval arithmetic, with the endpoints of FloatLib's exact
operations.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, 2026, <https://github.com/lean-dojo/FloatLib>. We use its expression
  language, its backends and their soundness theorems.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open FloatLib.Numerics.Interval (Backend)

/-! ## FloatLib's evaluation -/

section Evaluation

variable {κ : Type*}

/--
FloatLib's evaluation with the zero rule (`Expr.evalZero?`) of `expr` on the backend `B`, with
FloatLib's standard calls `π`, `x ^ y` and `e` at the accuracy settings `config`
(`Backend.Standard.extensions`). The expression is numbered by occurrence
(`Verified.Expr.numberOccurrences`): its `k`-th variable occurrence is the input `k`, which has
the interval of the label of that occurrence in `intervals`.
-/
def floatLibEval? (B : Backend ℚ) (config : Backend.Config)
    (intervals : κ → FloatLib.Numerics.Interval ℚ) (expr : Verified.Expr κ) :
    Option (FloatLib.Numerics.Interval ℚ) :=
  ((expr.numberOccurrences 0).toFloatLib id).evalZero?
    (B.withExtensions config Backend.Standard.extensions)
    fun k ↦ (expr.occurrences.map intervals)[k]?

/-- A successful `floatLibEval?` contains the value of `expr` at `ρ` when the interval of each
variable of `expr` contains its value at `ρ`, for a sound backend `B` that reads its rational
ends as themselves. This is `Verified.Expr.containsReal_evalZero?_numberOccurrences` on the box of
the occurrences (`Verified.Expr.containsReal_occurrences`). -/
theorem containsReal_floatLibEval? {B : Backend ℚ} (hB : B.Sound) (hdecode : B.decode = some)
    {config : Backend.Config} {intervals : κ → FloatLib.Numerics.Interval ℚ}
    {expr : Verified.Expr κ} {ρ : κ → ℝ}
    (hρ : ∀ i ∈ expr.occurrences, (intervals i).ContainsReal some (ρ i))
    {J : FloatLib.Numerics.Interval ℚ} (h : floatLibEval? B config intervals expr = some J) :
    J.ContainsReal some (expr.eval ρ) := by
  have hbox : ∀ k (K : FloatLib.Numerics.Interval ℚ),
      (expr.occurrences.map intervals)[k]? = some K →
        K.ContainsReal B.decode (Verified.Expr.occurrenceValues ρ expr k) := by
    rw [hdecode]
    exact Verified.Expr.containsReal_occurrences hρ
  have hJ := Verified.Expr.containsReal_evalZero?_numberOccurrences hB hbox h
  rwa [hdecode] at hJ

/-- A successful `floatLibEval?` has ordered ends when the interval of each variable of `expr`
has: it contains the value of `expr` at the lower corner of the box, where each variable takes the
lower end of its interval. -/
theorem lo_le_hi_of_floatLibEval? {B : Backend ℚ} (hB : B.Sound) (hdecode : B.decode = some)
    {config : Backend.Config} {intervals : κ → FloatLib.Numerics.Interval ℚ}
    {expr : Verified.Expr κ}
    (hordered : ∀ i ∈ expr.occurrences, (intervals i).lo ≤ (intervals i).hi)
    {J : FloatLib.Numerics.Interval ℚ} (h : floatLibEval? B config intervals expr = some J) :
    J.lo ≤ J.hi :=
  ordered_of_containsReal <| containsReal_floatLibEval? hB hdecode
    (ρ := fun i ↦ ((intervals i).lo : ℝ))
    (fun i hi ↦ (FloatLib.Numerics.Interval.containsReal_some_iff _ _).mpr
      ⟨le_rfl, by exact_mod_cast hordered i hi⟩) h

/--
FloatLib's evaluation `floatLibEval?` of `expr` on the backend `B`, with the standard calls at the
accuracy settings `config`, as an ordered rational interval. The variables of `expr` have the
intervals `intervals`, whose ends must be ordered (`hordered`), and `B` must be sound and read its
rational ends as themselves.

The order of the result comes from containment at the lower corner of the box
(`lo_le_hi_of_floatLibEval?`), so no comparison is evaluated. `evalWith_sound` encloses the value
of `expr` at every point of the box.
-/
def evalWith (B : Backend ℚ) (hB : B.Sound) (hdecode : B.decode = some)
    (config : Backend.Config) (intervals : κ → FloatLib.Numerics.Interval ℚ)
    (expr : Verified.Expr κ)
    (hordered : ∀ i ∈ expr.occurrences, (intervals i).lo ≤ (intervals i).hi) :
    Option RationalInterval :=
  match h : floatLibEval? B config intervals expr with
  | some J => some (ofFloatLib J (lo_le_hi_of_floatLibEval? hB hdecode hordered h))
  | none => none

/-- A successful `evalWith` contains the value of `expr` at `ρ` when the interval of each
variable of `expr` contains its value at `ρ`. -/
theorem evalWith_sound {B : Backend ℚ} {hB : B.Sound} {hdecode : B.decode = some}
    {config : Backend.Config} {intervals : κ → FloatLib.Numerics.Interval ℚ}
    {expr : Verified.Expr κ}
    {hordered : ∀ i ∈ expr.occurrences, (intervals i).lo ≤ (intervals i).hi} {ρ : κ → ℝ}
    (hρ : ∀ i ∈ expr.occurrences, (intervals i).ContainsReal some (ρ i)) {I : RationalInterval}
    (h : evalWith B hB hdecode config intervals expr hordered = some I) :
    I.MemReal (expr.eval ρ) := by
  unfold evalWith at h
  split at h
  · rename_i J hJ
    obtain rfl := Option.some.inj h
    exact (memReal_ofFloatLib_iff _ _ _).mpr (containsReal_floatLibEval? hB hdecode hρ hJ)
  · cases h

end Evaluation

/--
FloatLib's exact rational evaluation of `expr` on the environment `env`, after the
well-formedness check: `evalWith` on `Backend.rational` at FloatLib's default accuracy settings.

On literals, variables, sums, differences, products, negations and natural powers this is exact
rational interval arithmetic. The elementary functions come from FloatLib's table
`Backend.elementaryBounds?`, and `π`, `e` and real powers from FloatLib's standard calls. A quotient
whose denominator interval contains zero, or an elementary function outside the domain of its
enclosure, gives `none`, unless a factor that is exactly zero makes the result zero anyway.

`Verified.Expr.eval` is total, but a rational literal with denominator zero is not a
mathematically valid rational constant. The evaluation therefore rejects it rather than turning
Lean's totalized value into an analytic certificate.
-/
def evalPolynomial {ι : Type*} (env : ι → RationalInterval)
    (expr : Verified.Expr ι) : Option RationalInterval :=
  if expr.isWellFormed then
    evalWith Backend.rational Backend.rational_sound rfl {} (fun i ↦ (env i).toFloatLib) expr
      fun i _ ↦ (env i).hle
  else
    none

/-- A rational literal with denominator `0` is rejected by the polynomial evaluator. -/
@[simp] theorem evalPolynomial_rat_zero_den {ι : Type*} (env : ι → RationalInterval) (num : Int) :
    evalPolynomial env (.rat num 0) = none := rfl

/-- Successful polynomial interval evaluation encloses the corresponding real evaluation whenever
each variable lies in its assigned interval. -/
theorem evalPolynomial_sound {ι : Type*}
    (env : ι → RationalInterval) (ρ : ι → ℝ)
    (henv : ∀ i, (env i).MemReal (ρ i)) :
    ∀ expr I, evalPolynomial env expr = some I → I.MemReal (expr.eval ρ)
  | expr, I, h => by
    unfold evalPolynomial at h
    split_ifs at h
    exact evalWith_sound (fun i _ ↦ ((env i).toFloatLib_containsReal_iff _).mpr (henv i)) h

/-! ## Denominator lower bounds -/

/-- A positive rational proposed as an executable denominator lower bound.

Semantic validity for a particular expression and domain is supplied by
`ExprAbsLowerProvider.sound`; this payload is not a stand-alone certificate. -/
abbrev AbsLowerResult := {delta : ℚ // 0 < delta}

namespace AbsLowerResult

/-- Candidate rational bound later certified against a denominator's absolute value. -/
abbrev delta (result : AbsLowerResult) : ℚ :=
  result.1

/-- Positivity of the executable lower bound. -/
theorem pos (result : AbsLowerResult) : 0 < result.delta :=
  result.2

end AbsLowerResult

/-- A checked provider for denominator lower-bound certificates.

CEGA planners compile denominator facts into this callback object for the certified contexts of
`CAS.Continuum.IntervalEval.Context`: `lookup` is executable, while `sound` proves every emitted
certificate is valid on the current chart. -/
structure ExprAbsLowerProvider {α : Type*} {ι : Type*} (s : Set α) (ρ : α → ι → ℝ) where
  /-- Executable lookup for denominator lower bounds. -/
  lookup : Verified.Expr ι → Option AbsLowerResult
  /-- Every emitted executable certificate is semantically sound. -/
  sound :
    ∀ x, x ∈ s → ∀ den cert, lookup den = some cert →
      (cert.delta : ℝ) ≤ |den.eval (ρ x)|

/-! ## Finite denominator-provider entries -/

/--
One route-backed denominator side condition returned by a CEGA planner.

The entry stores the executable positive rational lower bound, its direct
semantic theorem for the indexed denominator, and the route provenance used
to obtain it.
-/
structure ExprAbsLowerRouteEntry {α : Type*} {ι : Type*} (s : Set α) (ρ : α → ι → ℝ) where
  /-- The denominator expression guarded by this entry. -/
  den : Verified.Expr ι
  /-- Positive rational lower bound used by interval division. -/
  bound : AbsLowerResult
  /-- The rational bound is valid for the denominator throughout the chart. -/
  sound : ∀ x, x ∈ s → (bound.delta : ℝ) ≤ |den.eval (ρ x)|
  /-- Route steps used to prove the side condition. -/
  steps : List RouteStep := []

namespace ExprAbsLowerProvider

variable {α : Type*} {ι : Type*} {s : Set α} {ρ : α → ι → ℝ}

/--
Build a denominator provider from a finite list of route-backed planner entries.

`List.findSome?` performs one tail-recursive first-match traversal. No
intermediate provider structures or fallback closures are allocated.
-/
def fromRouteEntries [DecidableEq ι]
    (entries : List (ExprAbsLowerRouteEntry s ρ)) :
    ExprAbsLowerProvider s ρ where
  lookup := fun den ↦
    entries.findSome? fun entry ↦
      if den = entry.den then some entry.bound else none
  sound := by
    intro x hx den cert hlookup
    obtain ⟨entry, _hentry, hentry⟩ :=
      List.exists_of_findSome?_eq_some hlookup
    by_cases hden : den = entry.den
    · simp only [ite_eq_left hden] at hentry
      have hcert := Option.some.inj hentry
      subst cert
      subst den
      exact entry.sound x hx
    · simp only [ite_eq_right hden] at hentry
      cases hentry

/-- Collect the route steps from a finite denominator-entry list. -/
def routeEntrySteps (entries : List (ExprAbsLowerRouteEntry s ρ)) : List RouteStep :=
  entries.flatMap fun entry ↦ entry.steps

end ExprAbsLowerProvider

end RationalInterval
end CAS.Continuum

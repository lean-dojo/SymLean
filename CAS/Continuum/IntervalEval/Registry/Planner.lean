/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalEval.Hyperbolic
public import CAS.Continuum.IntervalEval.Registry.Refinement
public import CAS.Continuum.IntervalEval.Attempt
public import CAS.Continuum.IntervalEval.WellFormed
public import CAS.Expr.FloatLib
public import FloatLib.Numerics.Enclosure.Affine.ExprProof

/-!
# Selecting certified enclosures

The planner chooses among the enclosure routes for an expression on a registry chart: exact
side-condition-aware normalization, affine arithmetic (`affineEnclosureAttempt?`), the
correlated hyperbolic ranges, and the interval route with automatically synthesized facts.
`selectFiniteEnclosurePreview?` computes the candidate intervals without proofs and ranks them
by `PlannerSummary.enclosureScore`, and `selectFiniteEnclosureAttempt?` builds the checked
`EnclosureAttempt` for the selected route. The ranking plays no part in soundness, which each
attempt carries itself. `selectEnclosureAttempt?` tries the exact normalization and then the
interval route, without ranking. `selectVariableSubdivisionChoice?` picks a coordinate for box
subdivision from first-order sensitivity scores.

The affine range is FloatLib's. `affineRange? box expr` translates `expr` into FloatLib's
expression language and takes `Expr.affineRange?` of `FloatLib.Numerics.Enclosure.Affine` on the
box of its variables, and `mem_affineRange_of_memBox` says that the range contains the value of
`expr` at every point of the box.

## Implementation notes

We run every finite-chart route without proofs, compare the intervals by width, then by the
largest absolute endpoint, then by route length, and build only the selected certificate; a
correlated hyperbolic route that succeeds is taken at once. The natural interval extension is
the `.easy` route: the expression is simplified, `extendWithEasyFacts?` adds the denominator
bounds it needs, and the certified context evaluates it. What the kernel checks is the selected
`EnclosureAttempt`, whose `sound` field is the inclusion theorem of its route (the soundness
theorems of the context, such as `CertifiedEvalContext.sound_simplified`, and
`mem_affineRange_of_memBox` for affine arithmetic). If the selected route fails to build, the
attempt is `none`; the box planner in `CAS.CEGA.Query` then tries its next candidate.

Affine arithmetic keeps the correlation between two occurrences of a variable only when they
share a noise symbol. So the translation for the affine route numbers the variables of `expr` by
their positions in `expr.occurrences.dedup`, one number for each variable, and FloatLib's box
holds their intervals in that order. FloatLib compiles the polynomial fragment (constants,
variables, sums, differences, negations, products and natural powers) and returns `none` on
every other operation. A rational literal with denominator zero gets no range either, as in the
other routes (`Verified.Expr.isWellFormed`). The range is a rational interval because it
contains the value of `expr` at the lower corner of the box, so no comparison is evaluated.

The subdivision choice is ours and untrusted. It proposes the coordinate with the largest
positive score `width(Bᵢ) · max |Dᵢ|` from `variableSensitivities`, ties broken by width. When
no score is positive it proposes the widest coordinate whose partial derivative could not be
enclosed. The cover by the two halves of a bisection is proved for every coordinate, so the
choice only affects sharpness.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, 2026, <https://github.com/lean-dojo/FloatLib>. We use its affine models
  and `Expr.containsReal_affineRange?`.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open CAS.Certificate
open CAS.Verified

/-! ### Affine ranges on FloatLib -/

section Affine

variable {ι : Type*}

/-- Two assignments that agree on the variables of `expr` give it the same value. -/
private theorem eval_congr_occurrences {ρ σ : ι → ℝ} :
    ∀ {expr : Verified.Expr ι}, (∀ i ∈ expr.occurrences, ρ i = σ i) →
      expr.eval ρ = expr.eval σ := by
  intro expr h
  induction expr with
  | var i => simpa [Verified.Expr.occurrences] using h
  | _ => simp_all [Verified.Expr.occurrences, or_imp, forall_and]

variable [DecidableEq ι]

/-- FloatLib's affine range of the translation of `expr` that numbers each variable by its
position in a list `vars` of all variables of `expr` contains the value of `expr` at every point
`x` of `box`. -/
private theorem containsReal_affineRange_of_vars {box : ι → RationalInterval}
    {expr : Verified.Expr ι} {vars : List ι} (hvars : ∀ i ∈ expr.occurrences, i ∈ vars)
    {I : FloatLib.Numerics.Interval ℚ}
    (h : FloatLib.Numerics.Enclosure.Affine.Expr.affineRange? (expr.toFloatLib vars.idxOf)
      (vars.map fun i ↦ (box i).toFloatLib) = some I)
    {x : ι → ℝ} (hx : ∀ i, (box i).MemReal (x i)) : I.ContainsReal some (expr.eval x) := by
  let values : ℕ → ℝ := fun k ↦ (vars[k]?.map x).getD 0
  have hbox : FloatLib.Numerics.Interval.Box.ContainsReal
      (vars.map fun i ↦ (box i).toFloatLib) values := by
    intro k J hJ
    rw [List.getElem?_map] at hJ
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 hJ
    simpa [values, hi] using ((box i).toFloatLib_containsReal_iff _).mpr (hx i)
  have hrange := FloatLib.Numerics.Enclosure.Affine.Expr.containsReal_affineRange? h hbox
    (FloatLib.Numerics.Interval.extensionValues
      FloatLib.Numerics.Interval.Backend.Standard.functions)
  rwa [expr.eval_toFloatLib vars.idxOf (fun i ↦ values (vars.idxOf i)) values fun _ ↦ rfl,
    eval_congr_occurrences (σ := x) fun i hi ↦ by
      simp [values, List.getElem?_idxOf (hvars i hi)]] at hrange

/--
FloatLib's affine range of `expr` on the rational box `box`, before the order of its ends is
attached.

The translation `Verified.Expr.toFloatLib` numbers the variables of `expr` by their positions
in `expr.occurrences.dedup`, so that every occurrence of one variable gets the same noise
symbol, and FloatLib's box holds their intervals in that order. The result is
`Expr.affineRange?` of `FloatLib.Numerics.Enclosure.Affine` on that expression and box: `none`
outside the polynomial fragment.
-/
def floatLibAffineRange? (box : ι → RationalInterval) (expr : Verified.Expr ι) :
    Option (FloatLib.Numerics.Interval ℚ) :=
  FloatLib.Numerics.Enclosure.Affine.Expr.affineRange?
    (expr.toFloatLib expr.occurrences.dedup.idxOf)
    (expr.occurrences.dedup.map fun i ↦ (box i).toFloatLib)

/-- A successful `floatLibAffineRange? box expr` contains the value of `expr` at every point `x`
of the box. This is FloatLib's `Expr.containsReal_affineRange?` after `eval_toFloatLib`. -/
theorem containsReal_floatLibAffineRange? {box : ι → RationalInterval}
    {expr : Verified.Expr ι} {I : FloatLib.Numerics.Interval ℚ}
    (h : floatLibAffineRange? box expr = some I) {x : ι → ℝ}
    (hx : ∀ i, (box i).MemReal (x i)) : I.ContainsReal some (expr.eval x) :=
  containsReal_affineRange_of_vars (fun _ ↦ List.mem_dedup.2) h hx

/--
The affine range of `expr` on the rational box `box`, or `none` when `expr` has a rational
literal with denominator zero or lies outside the polynomial fragment.

This is `floatLibAffineRange? box expr`, FloatLib's affine range of the translation, as a rational
interval. Its ends are ordered because it contains the value of `expr` at the lower corner of the
box (`containsReal_floatLibAffineRange?`).
-/
def affineRange? (box : ι → RationalInterval) (expr : Verified.Expr ι) :
    Option RationalInterval :=
  if expr.isWellFormed then
    match h : floatLibAffineRange? box expr with
    | none => none
    | some I =>
        some (ofFloatLib I (ordered_of_containsReal
          (containsReal_floatLibAffineRange? h fun i ↦ (box i).lo_memReal)))
  else
    none

/-- A successful affine range contains every evaluation on the original variable box. -/
theorem mem_affineRange_of_memBox (box : ι → RationalInterval) (expr : Verified.Expr ι)
    (range : RationalInterval) (x : ι → ℝ) (hx : ∀ i, (box i).MemReal (x i))
    (h : affineRange? box expr = some range) :
    range.MemReal (expr.eval x) := by
  unfold affineRange? at h
  split_ifs at h
  split at h
  · exact absurd h (by simp)
  · rename_i I hI
    obtain rfl := Option.some.inj h
    exact (memReal_ofFloatLib_iff _ _ _).mpr (containsReal_floatLibAffineRange? hI hx)

end Affine

namespace CertifiedEvalRegistry

variable {α : Type*} {ι : Type*} [DecidableEq ι] {s : Set α} {ρ : α → ι → ℝ}

/-! ### Canonical range selection -/

/--
Select a checked enclosure, trying side-condition-aware exact normalization
before the simplifying interval route with automatically synthesized facts.

Both branches return an attempt indexed by the original expression's semantic
function. The branch choice is planner behavior; soundness is carried by the
returned attempt itself.
-/
noncomputable def selectEnclosureAttempt?
    (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr ι) :
    Option (EnclosureAttempt α s (fun x ↦ expr.eval (ρ x))) :=
  let route := r.toRoute
  match route.cert.enclosureAttemptNormalized? expr route.steps with
  | some result => some result
  | none =>
      (r.extendWithEasyFacts? expr).bind fun fallback ↦
        fallback.toContext.enclosureAttemptSimplified? expr fallback.toRoute.steps

/-- The affine enclosure of `expr` on the chart of the registry: `affineRange?` on the chart's
interval environment, with `mem_affineRange_of_memBox` as its proof. -/
noncomputable def affineEnclosureAttempt?
    (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr ι) :
    Option (EnclosureAttempt α s (fun x ↦ expr.eval (ρ x))) :=
  match hRange : RationalInterval.affineRange? r.env expr with
  | none => none
  | some range =>
      some
        { interval := range
          sound := fun x hx ↦
            RationalInterval.mem_affineRange_of_memBox
              r.env expr range (ρ x) (r.hvars x hx) hRange
          steps := [.affineArithmetic] }

/-- Package a route's optional interval as a proof-free planner summary of the given `kind`,
recording the number of route `steps`. -/
def enclosurePreviewCandidate?
    (kind : PlannerRouteKind) (interval? : Option RationalInterval)
    (steps : List RouteStep) : Option PlannerSummary :=
  interval?.map fun interval ↦
    { kind := kind
      interval := interval
      stepCount := steps.length }

/-- Select the best proof-free finite-chart enclosure summary. -/
def selectFiniteEnclosurePreview? [Fintype ι]
    (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr ι) : Option PlannerSummary :=
  let route := r.toRoute
  let normalized := enclosurePreviewCandidate? .exact
    (route.cert.evalNormalized expr) (.exactNormalization :: route.steps)
  let affine := enclosurePreviewCandidate? .affine
    (RationalInterval.affineRange? r.env expr) [.affineArithmetic]
  let hyperbolic := enclosurePreviewCandidate? .hyperbolic
    (r.toContext.hyperbolicRange? expr r.precision.expOrder.toPNat') [.hyperbolicRange]
  let fallback := (r.extendWithEasyFacts? expr).bind fun extended ↦
    enclosurePreviewCandidate? .easy
      (extended.toContext.evalSimplified expr) extended.toRoute.steps
  PlannerSummary.bestEnclosure? [normalized, affine, hyperbolic, fallback].reduceOption

/--
Select a checked enclosure for a finite coordinate chart.

A successful correlated hyperbolic route is preferred immediately. Otherwise
the ranked preview chooses among side-condition-aware normalization, affine
arithmetic, and the simplifying interval fallback. This priority need not give
the narrowest of all candidate intervals. Every returned attempt carries its
own soundness proof; candidate scores do not participate in that proof.
-/
noncomputable def selectFiniteEnclosureAttempt? [Fintype ι]
    (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr ι) :
    Option (EnclosureAttempt α s (fun x ↦ expr.eval (ρ x))) :=
  match r.toContext.hyperbolicEnclosureAttempt? expr r.precision.expOrder.toPNat' with
  | some result => some result
  | none =>
      match (r.selectFiniteEnclosurePreview? expr).map PlannerSummary.kind with
      | some .exact =>
          let route := r.toRoute
          route.cert.enclosureAttemptNormalized? expr route.steps
      | some .affine => r.affineEnclosureAttempt? expr
      | some .hyperbolic =>
          r.toContext.hyperbolicEnclosureAttempt? expr r.precision.expOrder.toPNat'
      | some .easy =>
          (r.extendWithEasyFacts? expr).bind fun extended ↦
            extended.toContext.enclosureAttemptSimplified? expr extended.toRoute.steps
      | _ => none

/-! ### Sensitivity-guided subdivision choice -/

/-- Fallback subdivision candidate for coordinate `i`, scored by its source interval width.

The candidate is produced only when `expr` mentions `i`, the source interval of `i` is not
degenerate, and `sensitivities` holds no first-order score for `i`. -/
def unsupportedVariableSubdivisionChoice?
    (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr ι)
    (sensitivities : List (VariableSubdivisionChoice ι)) (i : ι) :
    Option (VariableSubdivisionChoice ι) :=
  let source := r.env i
  let width := source.hi - source.lo
  if expr.containsVar i && decide (source.lo < source.hi) &&
      !sensitivities.any (fun sensitivity ↦ sensitivity.coordinate == i) then
    some
      { coordinate := i
        priority := width
        width }
  else
    none

/--
Choose a coordinate for interval subdivision among `coordinates`.

Positive first-order influence scores are preferred. If interval evaluation
cannot enclose any relevant partial derivative, the widest unsupported
coordinate is selected. Coordinates whose checked derivative range is exactly
zero are not subdivided merely because they are syntactically present. The
caller enumerates the coordinates (see `variableSensitivities`).
-/
def selectVariableSubdivisionChoice?
    (r : CertifiedEvalRegistry s ρ) (coordinates : List ι) (expr : Verified.Expr ι) :
    Option (VariableSubdivisionChoice ι) :=
  let sensitivities := r.variableSensitivities coordinates expr
  let positive := sensitivities.filter (fun sensitivity ↦ decide (0 < sensitivity.priority))
  let score := fun choice : VariableSubdivisionChoice ι ↦
    (toLex (choice.priority, choice.width) : ℚ ×ₗ ℚ)
  match positive.argmax score with
  | some sensitivity => some sensitivity
  | none =>
      (coordinates.filterMap
        (r.unsupportedVariableSubdivisionChoice? expr sensitivities)).argmax score

end CertifiedEvalRegistry
end RationalInterval
end CAS.Continuum

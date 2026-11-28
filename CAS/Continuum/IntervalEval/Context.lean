/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Certificate.Residual
public import CAS.Continuum.IntervalEval.Core
public import CAS.Continuum.IntervalEval.Normalization
public import CAS.Continuum.IntervalEval.Planning.Precision
public import CAS.Route.Core
public import FloatLib.Numerics.Enclosure.Expression.ElementaryTableProof
public import FloatLib.Numerics.Enclosure.Interval.RoundingProof

/-!
# Certified interval-evaluation contexts

A certified context bundles, for one chart, a rational interval environment with the proof that
it encloses every chart point, a provider of lower bounds on the absolute values of
denominators, and a precision policy. FloatLib evaluates every expression, on the backend
`Precision.backend` of the policy. Successful evaluation is exposed through typed attempts whose
certificates refer to the displayed intervals and original functions. Route steps are diagnostic
metadata.

## Main definitions

* `Precision.backend`: FloatLib's backend for certified evaluation at a precision policy.
* `CertifiedEvalContext`: an interval environment with its variable enclosure proof, a
  denominator provider and a precision policy.
* `CertifiedEvalContext.eval`, `evalSimplified`, `evalNormalized`: the bundled
  evaluator, the simplify-first variant, and the side-condition-aware exact
  normalization variant (which can certify cancellations such as `x / x = 1`
  when the context proves `x ≠ 0`).
* `EnclosureAttempt`: the certificate-carrying result type, and the constructors
  `enclosureAttemptSimplified?` and `enclosureAttemptNormalized?` that produce
  enclosure attempts.
* `rangeSteps`: the route steps that name the elementary enclosures of an evaluation.

## Main results

* `CertifiedEvalContext.sound`, `sound_simplified`, `sound_normalized`: each
  successful evaluation encloses `expr.eval (ρ x)` at every chart point.
* `CertifiedEvalContext.eval_ne_zero_of_certifiesNonzero`: a successful nonzero
  check proves the expression nonzero on the whole chart.

## Implementation notes

`CertifiedEvalContext.eval` first evaluates the expression with the chart interval of each
variable (`evalWith`). A denominator bound `δ ≤ |b|` from the provider usually holds only on the
chart, while a backend of FloatLib has to enclose its operations at every member of their input
intervals, so the bound cannot be an enclosure of FloatLib. When the first evaluation fails, a
quotient `a / b` with a registered bound is therefore written as `a * w`, where `w` is a fresh
variable for `b⁻¹` with the interval `[-1/δ, 1/δ]` (`Verified.Expr.lowerDivisions`), and the
expression is evaluated again. The bound enters through the proof that `w` lies in its interval
at every chart point (`Verified.Expr.containsReal_loweredIntervals`). The first evaluation is
sharper when the interval of a denominator excludes zero, which is why it comes first. FloatLib
computes the ranges of the unary operations from the intervals of their arguments, so the
context needs no facts about them.

Computable previews are kept separate from the attempts. A preview may guide search, but only a
certificate-producing operation supports a mathematical conclusion: an `EnclosureAttempt` stores
its interval with `EnclosedOn fn s lo hi` for the function named in its type, and all three
evaluators rest on `evalWith_sound`. Simplifying before evaluation removes cancellations such as
`x - x`, whose interval evaluation is `[lo - hi, hi - lo]` rather than `0`; it is an
unconditional equality of semantics. The normalization `intervalNormalizeWithSide` may also
cancel a common factor, and `evalNormalized` uses its result only after `certifiesSideConditions`
proves every emitted `e ≠ 0` on the chart, by a registered lower bound on `|e|` or by an interval
of `e` that excludes zero.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open CAS.Certificate
open FloatLib.Numerics.Interval (Backend)

/-! ## FloatLib's backend for certified contexts -/

/--
FloatLib's backend for certified evaluation at the precision policy `precision`. The algebraic
operations, reciprocals and quotients are exact rational arithmetic. The elementary functions are
FloatLib's table at the setting `precision.toSetting`, with their ends rounded outward to about
128 significant bits (`OutwardRounding.relative`), so that a small value keeps its relative
accuracy: `exp (-200)` keeps 128 significant bits, where a grid of spacing `2 ^ (-128)` would
widen it to `[0, 2 ^ (-128)]`. The standard calls `π`, `x ^ y` and `e` are added when an expression
is evaluated (`floatLibEval?`), at the accuracy settings `precision.toConfig`.
-/
def Precision.backend (precision : Precision) : Backend ℚ :=
  Backend.ofRoundings FloatLib.Numerics.Interval.Internal.rationalOutwardRounding
    FloatLib.Numerics.Interval.Internal.rationalOutwardRounding
    (FloatLib.Numerics.OutwardRounding.relative 128)
    (Backend.elementaryWith precision.toSetting)

/-- Every operation of `Precision.backend` encloses its real result (`Backend.ofRoundings_sound`
with `Backend.containsReal_elementaryWith`). -/
theorem Precision.backend_sound (precision : Precision) : precision.backend.Sound :=
  Backend.ofRoundings_sound _ _ _ _ rfl rfl (Backend.containsReal_elementaryWith _)

/-- `Precision.backend` reads its rational ends as themselves. -/
theorem Precision.backend_decode (precision : Precision) : precision.backend.decode = some :=
  rfl

/-! ## Route steps -/

/-- The route steps that name the elementary enclosures of FloatLib that an evaluation of `expr`
uses, in the order of the evaluation: one range step for each square root, arctangent, arcsine,
arccosine, exponential and logarithm, and a logarithm and an exponential range for each real
power. Steps are diagnostic metadata for `cega?` reports and prove nothing. -/
def rangeSteps {κ : Type*} : Verified.Expr κ → List RouteStep
  | .nat _ | .int _ | .rat _ _ | .pi | .e | .var _ => []
  | .add a b | .mul a b | .sub a b | .div a b => rangeSteps a ++ rangeSteps b
  | .neg a | .pow a _ | .sin a | .cos a => rangeSteps a
  | .sqrt a => rangeSteps a ++ [.sqrtRange]
  | .atan a => rangeSteps a ++ [.atanRange]
  | .asin a => rangeSteps a ++ [.asinRange]
  | .acos a => rangeSteps a ++ [.acosRange]
  | .exp a => rangeSteps a ++ [.expRange]
  | .log a => rangeSteps a ++ [.logRange]
  | .rpow a b => rangeSteps a ++ rangeSteps b ++ [.logRange, .expRange]

/-! ## Certified evaluation plans and successful attempts -/

/-
The attempt records of this section are structures whose mathematical content is stated
directly for the indexed function and displayed interval, so function and
endpoint coherence hold by construction. Route steps only record how the
attempt was found.
-/

/-- A bundled CEGA plan for certified interval evaluation on one chart.

The registry planner synthesizes this certified evaluation context. It carries:

* a variable interval environment;
* a theorem that every point of the chart satisfies that environment;
* a provider of lower bounds on the absolute values of denominators, proved on the chart;
* the precision policy of FloatLib's backend (`Precision.backend`).

Its evaluator and soundness methods bundle these into one certificate-producing API, with
`evalWith_sound` as the underlying soundness theorem.
-/
structure CertifiedEvalContext {α : Type*} {ι : Type*} (s : Set α) (ρ : α → ι → ℝ) where
  /-- Rational interval environment for the chart variables. -/
  env : ι → RationalInterval
  /-- Every chart point satisfies the variable interval environment. -/
  hvars : ∀ x, x ∈ s → ∀ i, (env i).MemReal (ρ x i)
  /-- Certified denominator lower-bound provider. -/
  divProvider : ExprAbsLowerProvider s ρ
  /-- Precision policy of FloatLib's backend. -/
  precision : Precision := {}

/-- A successful enclosure attempt for `fn`, with its checked interval and construction steps. -/
structure EnclosureAttempt (α : Type*) (s : Set α) (fn : α → ℝ) where
  /-- The interval computed by the evaluator. -/
  interval : RationalInterval
  /-- The displayed interval encloses the function named by the attempt type. -/
  sound : EnclosedOn fn s (interval.lo : ℝ) (interval.hi : ℝ)
  /-- Route steps used to assemble the plan. -/
  steps : List RouteStep := []

/-! ## Route-plan previews and certified attempts -/

namespace CertifiedEvalContext

variable {α : Type*} {ι : Type*} {s : Set α} {ρ : α → ι → ℝ}

/-- Build a certified evaluation plan from finite planner-output entries, at the precision
policy `precision`. -/
def fromRouteEntries [DecidableEq ι]
    (env : ι → RationalInterval)
    (hvars : ∀ x, x ∈ s → ∀ i, (env i).MemReal (ρ x i))
    (divEntries : List (ExprAbsLowerRouteEntry s ρ)) (precision : Precision := {}) :
    CertifiedEvalContext s ρ where
  env := env
  hvars := hvars
  divProvider := ExprAbsLowerProvider.fromRouteEntries divEntries
  precision := precision

/-- The registered lower bound `δ ≤ |den|` of a denominator, as `Verified.Expr.lowerDivisions`
reads it. -/
def denominatorBound (p : CertifiedEvalContext s ρ) (den : Verified.Expr ι) : Option ℚ :=
  (p.divProvider.lookup den).map AbsLowerResult.delta

/-- Every bound of `denominatorBound` is positive and bounds the absolute value of its
denominator at every chart point. -/
theorem denominatorBound_spec (p : CertifiedEvalContext s ρ) {x : α} (hx : x ∈ s)
    (den : Verified.Expr ι) (δ : ℚ) (h : p.denominatorBound den = some δ) :
    0 < δ ∧ (δ : ℝ) ≤ |den.eval (ρ x)| := by
  obtain ⟨bound, hbound, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨bound.pos, p.divProvider.sound x hx den bound hbound⟩

/-- The intervals of the variables of `expr.lowerDivisions p.denominatorBound` have ordered ends:
the chart intervals, and `[-1/δ, 1/δ]` for a positive bound `δ`. -/
theorem loweredIntervals_lo_le_hi (p : CertifiedEvalContext s ρ) (expr : Verified.Expr ι) :
    ∀ l ∈ (expr.lowerDivisions p.denominatorBound).occurrences,
      (Verified.Expr.loweredIntervals (fun i ↦ (p.env i).toFloatLib) l).lo ≤
        (Verified.Expr.loweredIntervals (fun i ↦ (p.env i).toFloatLib) l).hi :=
  Verified.Expr.forall_mem_occurrences_lowerDivisions (fun i _ ↦ (p.env i).hle)
    fun den δ h ↦ by
      obtain ⟨bound, -, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [Verified.Expr.loweredIntervals, Sum.elim_inr,
        FloatLib.Numerics.Kernel.Q.neg_eq, FloatLib.Numerics.Kernel.Q.inv_eq]
      exact neg_le_self (inv_nonneg.mpr bound.pos.le)

/--
Run the certified interval evaluator: FloatLib's evaluation of `expr` on `Precision.backend` at
the precision policy of the context, with the chart interval of each variable (`evalWith`).

When that evaluation fails and the provider bounds some denominator of `expr`, the expression is
evaluated again with each quotient `a / b` whose denominator has a registered bound `δ ≤ |b|`
written as `a * w`, where `w` is a fresh variable with the interval `[-1/δ, 1/δ]`
(`Verified.Expr.lowerDivisions`). A rational literal with denominator zero gives `none`.
-/
def eval (p : CertifiedEvalContext s ρ) (expr : Verified.Expr ι) : Option RationalInterval :=
  if expr.isWellFormed then
    match evalWith p.precision.backend p.precision.backend_sound p.precision.backend_decode
        p.precision.toConfig (fun i ↦ (p.env i).toFloatLib) expr (fun i _ ↦ (p.env i).hle) with
    | some I => some I
    | none =>
      if (expr.lowerDivisions p.denominatorBound).occurrences.any Sum.isRight then
        evalWith p.precision.backend p.precision.backend_sound p.precision.backend_decode
          p.precision.toConfig (Verified.Expr.loweredIntervals fun i ↦ (p.env i).toFloatLib)
          (expr.lowerDivisions p.denominatorBound) (p.loweredIntervals_lo_le_hi expr)
      else
        none
  else
    none

/-- Check intrinsic syntax, simplify, then run the certified interval evaluator.

This is the dependency-aware planner entry point: exact symbolic rewriting gets
the first chance to remove cancellations such as `x - x`, and only the simplified
expression is sent to interval evaluation. The well-formedness check happens
first, so simplification cannot erase a malformed rational literal.
-/
def evalSimplified [DecidableEq ι]
    (p : CertifiedEvalContext s ρ) (expr : Verified.Expr ι) : Option RationalInterval :=
  if expr.isWellFormed then
    p.eval (Verified.Expr.simplify expr)
  else
    none

/--
Check one nonzero obligation using all evidence already in the context.

A registered absolute lower bound is preferred. If no such entry exists, the
ordinary interval evaluator may still prove nonvanishing by placing the whole
range strictly to one side of zero.
-/
def certifiesNonzero
    (p : CertifiedEvalContext s ρ) (expr : Verified.Expr ι) : Bool :=
  match p.divProvider.lookup expr with
  | some _ => true
  | none =>
      match p.eval expr with
      | some I => decide (I.hi < 0 ∨ 0 < I.lo)
      | none => false

/-- Check every nonzero obligation, allowing a different evidence source for
each expression. -/
def certifiesSideConditions
    (p : CertifiedEvalContext s ρ) (side : List (Verified.Expr ι)) : Bool :=
  side.all p.certifiesNonzero

/-- Run the checked side-aware simplification pipeline, check every side condition it emits
(`certifiesSideConditions`), then evaluate the transformed expression.

This is stronger than `evalSimplified`: it can certify cancellations such as
`x / x = 1` on a chart where the registry proves `x ≠ 0`. Intrinsically
malformed expressions and unproved side conditions are rejected.
-/
def evalNormalized [DecidableEq ι]
    (p : CertifiedEvalContext s ρ) (expr : Verified.Expr ι) :
    Option RationalInterval :=
  if expr.isWellFormed then
    let result := intervalNormalizeWithSide expr
    if p.certifiesSideConditions result.nonzero then
      p.eval result.expr
    else
      none
  else
    none

/-- Soundness of the bundled evaluator at a concrete chart point. -/
theorem sound (p : CertifiedEvalContext s ρ) (x : α) (hx : x ∈ s)
    (expr : Verified.Expr ι) (I : RationalInterval)
    (hEval : p.eval expr = some I) :
    I.MemReal (expr.eval (ρ x)) := by
  have hvars : ∀ i ∈ expr.occurrences, (p.env i).toFloatLib.ContainsReal some (ρ x i) :=
    fun i _ ↦ ((p.env i).toFloatLib_containsReal_iff _).mpr (p.hvars x hx i)
  unfold eval at hEval
  split at hEval
  next =>
    split at hEval
    next J hJ =>
      obtain rfl := Option.some.inj hEval
      exact evalWith_sound hvars hJ
    next =>
      split at hEval
      next =>
        have hmem := evalWith_sound
          (Verified.Expr.containsReal_loweredIntervals hvars (p.denominatorBound_spec hx)) hEval
        rwa [Verified.Expr.eval_lowerDivisions] at hmem
      next => cases hEval
  next => cases hEval

/-- A successful combined check proves one expression nonzero throughout the
context domain. -/
theorem eval_ne_zero_of_certifiesNonzero
    (p : CertifiedEvalContext s ρ) (expr : Verified.Expr ι)
    (hcheck : p.certifiesNonzero expr = true)
    (x : α) (hx : x ∈ s) : expr.eval (ρ x) ≠ 0 := by
  unfold certifiesNonzero at hcheck
  cases hlookup : p.divProvider.lookup expr with
  | some cert =>
      exact abs_pos.mp
        ((Rat.cast_pos.mpr cert.pos).trans_le (p.divProvider.sound x hx expr cert hlookup))
  | none =>
      cases hEval : p.eval expr with
      | none => simp [hlookup, hEval] at hcheck
      | some I =>
          have hmem := p.sound x hx expr I hEval
          have houtside : I.hi < 0 ∨ 0 < I.lo := by simpa [hlookup, hEval] using hcheck
          rcases houtside with hneg | hpos
          · exact (hmem.2.trans_lt (Rat.cast_lt_zero.mpr hneg)).ne
          · exact ((Rat.cast_pos.mpr hpos).trans_le hmem.1).ne'

/-- A successful combined check discharges every exact-normalization side
condition throughout the context domain. -/
theorem sideHolds_of_certifiesSideConditions
    (p : CertifiedEvalContext s ρ) (side : List (Verified.Expr ι))
    (hcheck : p.certifiesSideConditions side = true)
    (x : α) (hx : x ∈ s) :
    Verified.Expr.Alg.SideHolds (ρ x) side := fun expr hexpr ↦
  p.eval_ne_zero_of_certifiesNonzero expr (List.all_eq_true.mp hcheck expr hexpr) x hx

/-- Soundness of the simplify-then-evaluate path at a concrete chart point. -/
theorem sound_simplified [DecidableEq ι]
    (p : CertifiedEvalContext s ρ) (x : α) (hx : x ∈ s)
    (expr : Verified.Expr ι) (I : RationalInterval)
    (hEval : p.evalSimplified expr = some I) :
    I.MemReal (expr.eval (ρ x)) := by
  unfold evalSimplified at hEval
  split_ifs at hEval
  simpa using p.sound x hx _ I hEval

/-- Soundness of checked side-condition-aware normalization followed by
interval evaluation. -/
theorem sound_normalized [DecidableEq ι]
    (p : CertifiedEvalContext s ρ) (x : α) (hx : x ∈ s)
    (expr : Verified.Expr ι) (I : RationalInterval)
    (hEval : p.evalNormalized expr = some I) :
    I.MemReal (expr.eval (ρ x)) := by
  unfold evalNormalized at hEval
  dsimp only at hEval
  split_ifs at hEval with hwf hcovered
  exact eval_intervalNormalizeWithSide (ρ x) expr
    (p.sideHolds_of_certifiesSideConditions _ hcovered x hx) ▸ p.sound x hx _ I hEval

/-- Bundled certified interval evaluation gives a CEGA two-sided enclosure. -/
theorem enclosedOn (p : CertifiedEvalContext s ρ) (expr : Verified.Expr ι) (I : RationalInterval)
    (hEval : p.eval expr = some I) :
    EnclosedOn (fun x ↦ expr.eval (ρ x)) s (I.lo : ℝ) (I.hi : ℝ) :=
  RealIntervalBackend.enclosedOn_of_memReal (I := I) fun x hx ↦ p.sound x hx expr I hEval

/-- Simplify-then-evaluate gives a CEGA two-sided enclosure for the original expression. -/
theorem enclosedOn_simplified [DecidableEq ι]
    (p : CertifiedEvalContext s ρ) (expr : Verified.Expr ι) (I : RationalInterval)
    (hEval : p.evalSimplified expr = some I) :
    EnclosedOn (fun x ↦ expr.eval (ρ x)) s (I.lo : ℝ) (I.hi : ℝ) :=
  RealIntervalBackend.enclosedOn_of_memReal (I := I) fun x hx ↦ p.sound_simplified x hx expr I hEval

/-- Simplify and enclose an expression while certifying the original expression. The attempt
records the given steps, then the range steps (`rangeSteps`) of the simplified expression after
the lowering of its registered denominators. -/
noncomputable def enclosureAttemptSimplified? [DecidableEq ι]
    (p : CertifiedEvalContext s ρ) (expr : Verified.Expr ι)
    (steps : List RouteStep := []) :
    Option (EnclosureAttempt α s (fun x ↦ expr.eval (ρ x))) :=
  match hEval : p.evalSimplified expr with
  | some I =>
      some
        { interval := I
          sound := p.enclosedOn_simplified expr I hEval
          steps := steps ++
            rangeSteps ((Verified.Expr.simplify expr).lowerDivisions p.denominatorBound) }
  | none => none

/-- Normalize with checked side conditions and enclose the original expression. The attempt
records `.exactNormalization`, the given steps, then the range steps (`rangeSteps`) of the
normalized expression after the lowering of its registered denominators. -/
noncomputable def enclosureAttemptNormalized? [DecidableEq ι]
    (p : CertifiedEvalContext s ρ) (expr : Verified.Expr ι)
    (steps : List RouteStep := []) :
    Option (EnclosureAttempt α s (fun x ↦ expr.eval (ρ x))) :=
  match hEval : p.evalNormalized expr with
  | some I =>
      some
        { interval := I
          sound :=
            RealIntervalBackend.enclosedOn_of_memReal (I := I)
              (fun x hx ↦ p.sound_normalized x hx expr I hEval)
          steps := .exactNormalization :: steps ++
            rangeSteps ((intervalNormalizeWithSide expr).expr.lowerDivisions
              p.denominatorBound) }
  | none => none

end CertifiedEvalContext

end RationalInterval
end CAS.Continuum

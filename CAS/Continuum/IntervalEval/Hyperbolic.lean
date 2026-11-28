/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Elementary.Exp
public import CAS.Continuum.IntervalEval.Context
public import FloatLib.Numerics.Enclosure.Interval.HyperbolicProof

/-!
# Correlated ranges for lowered hyperbolic expressions

The expression syntax lowers `sinh a`, `cosh a` and `tanh a` to `(exp a - exp (-a)) / 2`,
`(exp a + exp (-a)) / 2` and their quotient. Evaluating these forms operation by operation
treats the two exponentials as independent and overestimates the range.
`hyperbolicEnclosureAttempt?` recognizes exactly these forms, encloses `a` with
`evalNormalized`, and applies FloatLib's enclosure `sinhBounds`, `coshBounds` or `tanhBounds`
at the requested positive Taylor order. `hyperbolicRange?` computes the same interval without
the proof.

## Implementation notes

The ranges are FloatLib's enclosures of `sinh`, `cosh` and `tanh`; we only recognize the lowered
syntax, which must use one argument expression in every exponential, and rewrite the semantics
with `Real.sinh_eq`, `Real.cosh_eq` and `Real.tanh_eq`. Treating the two exponentials as one
function removes the dependency between them. `ofTotalBounds` reads FloatLib's enclosure as a
rational interval: its ends are ordered because it contains the function at the lower end of the
argument interval, so no comparison is evaluated. The three attempts are `hyperbolicAttempt?`
with the equation between the lowered form and the function. The registry planner takes this
route at once when it applies.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, 2026, <https://github.com/lean-dojo/FloatLib>. We use its enclosures
  `Interval.sinhBounds`, `Interval.coshBounds` and `Interval.tanhBounds`.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open CAS.Certificate
open CAS.Verified
open FloatLib.Numerics.Interval (sinhBounds coshBounds tanhBounds containsReal_sinhBounds
  containsReal_coshBounds containsReal_tanhBounds)

/--
FloatLib's enclosure `bounds I order` on `I`, as a rational interval. `hbounds` says that
`bounds` encloses a real function `f`: `bounds J n` contains `f x` for every real member `x` of
`J` and every `n`. So the enclosure contains `f` at the lower end of `I`, and its ends are
ordered. The function `f` is part of the proof, so computing the interval never needs it.
-/
def ofTotalBounds (bounds : FloatLib.Numerics.Interval ℚ → ℕ → FloatLib.Numerics.Interval ℚ)
    (hbounds : ∃ f : ℝ → ℝ, ∀ J n {x : ℝ}, J.ContainsReal some x →
      (bounds J n).ContainsReal some (f x))
    (order : ℕ+) (I : RationalInterval) : RationalInterval :=
  ofFloatLib (bounds I.toFloatLib order) <| by
    obtain ⟨_, hf⟩ := hbounds
    exact ordered_of_containsReal (hf _ _ ((I.toFloatLib_containsReal_iff _).mpr I.lo_memReal))

/-- `ofTotalBounds bounds ⟨f, hbounds⟩ order I` contains `f x` for every `x ∈ I`. -/
theorem memReal_ofTotalBounds {f : ℝ → ℝ}
    {bounds : FloatLib.Numerics.Interval ℚ → ℕ → FloatLib.Numerics.Interval ℚ}
    (hbounds : ∀ J n {x : ℝ}, J.ContainsReal some x → (bounds J n).ContainsReal some (f x))
    (order : ℕ+) {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    (ofTotalBounds bounds ⟨f, hbounds⟩ order I).MemReal (f x) :=
  (memReal_ofFloatLib_iff _ _ _).mpr (hbounds _ _ ((I.toFloatLib_containsReal_iff x).mpr hx))

namespace CertifiedEvalContext

variable {α : Type*} {ι : Type*} [DecidableEq ι] {s : Set α} {ρ : α → ι → ℝ}

/--
The checked enclosure of a function `fn` on the chart with `fn x = f (arg.eval (ρ x))`, where
FloatLib's `bounds` encloses `f` (`hbounds`): `arg` is enclosed by `evalNormalized`, and the
result is `ofTotalBounds` of that interval. The route step is `.hyperbolicRange`.
-/
noncomputable def hyperbolicAttempt? (p : CertifiedEvalContext s ρ) (arg : Verified.Expr ι)
    {f : ℝ → ℝ} {bounds : FloatLib.Numerics.Interval ℚ → ℕ → FloatLib.Numerics.Interval ℚ}
    (hbounds : ∀ J n {x : ℝ}, J.ContainsReal some x → (bounds J n).ContainsReal some (f x))
    {fn : α → ℝ} (hfn : ∀ x, fn x = f (arg.eval (ρ x))) (order : ℕ+) :
    Option (EnclosureAttempt α s fn) :=
  match harg : p.evalNormalized arg with
  | none => none
  | some input =>
      some
        { interval := ofTotalBounds bounds ⟨f, hbounds⟩ order input
          sound := fun x hx ↦ by
            rw [hfn x]
            exact memReal_ofTotalBounds hbounds order (p.sound_normalized x hx arg input harg)
          steps := [.hyperbolicRange] }

/-- Checked enclosure of the lowered `sinh arg`, written `(exp arg - exp (-arg)) / 2`. The
argument is enclosed by `evalNormalized`, and the result is FloatLib's `sinhBounds` of that
interval. -/
noncomputable def sinhAttempt?
    (p : CertifiedEvalContext s ρ) (arg : Verified.Expr ι)
    (order : ℕ+ := defaultExpTaylorOrder.toPNat') :
    Option
      (EnclosureAttempt α s
        (fun x ↦
          (Verified.Expr.div
            (.sub (.exp arg) (.exp (.neg arg))) (.nat 2)).eval (ρ x))) :=
  p.hyperbolicAttempt? arg containsReal_sinhBounds (fun _ ↦ by simp [Real.sinh_eq]) order

/-- Checked enclosure of the lowered `cosh arg`, written `(exp arg + exp (-arg)) / 2`. The
argument is enclosed by `evalNormalized`, and the result is FloatLib's `coshBounds` of that
interval. -/
noncomputable def coshAttempt?
    (p : CertifiedEvalContext s ρ) (arg : Verified.Expr ι)
    (order : ℕ+ := defaultExpTaylorOrder.toPNat') :
    Option
      (EnclosureAttempt α s
        (fun x ↦
          (Verified.Expr.div
            (.add (.exp arg) (.exp (.neg arg))) (.nat 2)).eval (ρ x))) :=
  p.hyperbolicAttempt? arg containsReal_coshBounds (fun _ ↦ by simp [Real.cosh_eq]) order

/-- Checked enclosure of the lowered `tanh left`, written as the quotient of the lowered `sinh`
and `cosh` forms. The equality hypotheses identify `right`, `denominatorLeft`, and
`denominatorRight` with `left`, whose `evalNormalized` interval is passed to FloatLib's
`tanhBounds`. -/
noncomputable def tanhAttempt?
    (p : CertifiedEvalContext s ρ)
    (left right denominatorLeft denominatorRight : Verified.Expr ι)
    (hright : left = right) (hleft : left = denominatorLeft)
    (hdenominatorRight : left = denominatorRight)
    (order : ℕ+ := defaultExpTaylorOrder.toPNat') :
    Option
      (EnclosureAttempt α s
        (fun x ↦
          (Verified.Expr.div
            (.div (.sub (.exp left) (.exp (.neg right))) (.nat 2))
            (.div
              (.add (.exp denominatorLeft) (.exp (.neg denominatorRight)))
              (.nat 2))).eval (ρ x))) :=
  p.hyperbolicAttempt? left containsReal_tanhBounds (order := order) fun _ ↦ by
    subst right denominatorLeft denominatorRight
    simp only [Verified.Expr.eval, Nat.cast_ofNat, Real.tanh_eq]
    field_simp

/-- Preview the correlated range of a lowered `sinh`, `cosh`, or `tanh` expression. -/
def hyperbolicRange?
    (p : CertifiedEvalContext s ρ) (expr : Verified.Expr ι)
    (order : ℕ+ := defaultExpTaylorOrder.toPNat') : Option RationalInterval :=
  match expr with
  | .div (.sub (.exp left) (.exp (.neg right))) (.nat 2) =>
      if left = right then
        (p.evalNormalized left).map
          (ofTotalBounds sinhBounds ⟨_, containsReal_sinhBounds⟩ order)
      else
        none
  | .div (.add (.exp left) (.exp (.neg right))) (.nat 2) =>
      if left = right then
        (p.evalNormalized left).map
          (ofTotalBounds coshBounds ⟨_, containsReal_coshBounds⟩ order)
      else
        none
  | .div
      (.div (.sub (.exp left) (.exp (.neg right))) (.nat 2))
      (.div (.add (.exp denominatorLeft) (.exp (.neg denominatorRight))) (.nat 2)) =>
      if left = right ∧ left = denominatorLeft ∧ left = denominatorRight then
        (p.evalNormalized left).map
          (ofTotalBounds tanhBounds ⟨_, containsReal_tanhBounds⟩ order)
      else
        none
  | _ => none

/-- Build the checked correlated enclosure of a lowered hyperbolic expression. -/
noncomputable def hyperbolicEnclosureAttempt?
    (p : CertifiedEvalContext s ρ) (expr : Verified.Expr ι)
    (order : ℕ+ := defaultExpTaylorOrder.toPNat') :
    Option (EnclosureAttempt α s (fun x ↦ expr.eval (ρ x))) :=
  match expr with
  | .div (.sub (.exp left) (.exp (.neg right))) (.nat 2) =>
      if h : left = right then
        h ▸ p.sinhAttempt? left order
      else
        none
  | .div (.add (.exp left) (.exp (.neg right))) (.nat 2) =>
      if h : left = right then
        h ▸ p.coshAttempt? left order
      else
        none
  | .div
      (.div (.sub (.exp left) (.exp (.neg right))) (.nat 2))
      (.div (.add (.exp denominatorLeft) (.exp (.neg denominatorRight))) (.nat 2)) =>
      if h : left = right ∧ left = denominatorLeft ∧ left = denominatorRight then
        p.tanhAttempt? left right denominatorLeft denominatorRight h.1 h.2.1 h.2.2 order
      else
        none
  | _ => none

end CertifiedEvalContext
end RationalInterval
end CAS.Continuum

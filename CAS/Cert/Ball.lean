/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Elaboration.RealExpression.Operation
public import CAS.Numerics.GridBallRange

/-!
# Real expressions evaluated on balls

## Motivation

A numerical certificate states inequalities between real numbers that are built from stored
data by arithmetic, square roots and a few elementary functions. Which single evaluator, sound
once and for all, turns such an expression and enclosures of its data into an enclosure of its
value, at the cost of a few natural-number operations of the kernel per node?

## The idea

The expressions are those of SymLean, `CAS.Verified.Expr ι`, with their real value
`Verified.Expr.eval`; nothing is added to the syntax. The data enter through an environment
`benv : ι → GridBall`, one ball for every variable. `ball P benv e` replaces every operation of
`e` by the operation on balls of [GridBall](../Numerics/GridBall.lean) at precision `P`. A step
that cannot be decided, such as a denominator whose sign the ball does not decide or a real
power, returns an invalid ball, and a comparison fails when one of its two balls is invalid. So
the evaluator is total and has no error value. An invalid ball stays invalid through every
operation except the power `0`, which is the ball of `1` for every base.

The absolute value is written `√(a ^ 2)`, the form of SymLean's reifier
(`DesugaredFunction.desugar .abs`, here `absE`), and evaluated as the absolute value of the ball
of `a`, without a square root. Minimum and maximum are written through it (`maxE`, `minE`).

## Main results

* `ball_encloses` (all expressions, all environments, all precisions): if `benv i` encloses the
  real `ρ i` for every variable `i`, then `ball P benv e` encloses `e.eval ρ`.
* `eval_absE`, `eval_maxE`, `eval_minE`: the three derived forms denote `|a|`, `max a b` and
  `min a b`.

## Relations

`ball_encloses` is the induction over the expression with one theorem of
[GridBallReal](../Numerics/GridBallReal.lean) and [GridBallRange](../Numerics/GridBallRange.lean)
per constructor. `VerifiedExprIntervalEvaluator.rational`
([Range](../Continuum/IntervalEval/Range.lean)) uses exact rational intervals and `Option`; the
ball evaluator uses a validity flag. `CAS.Cert.Cond.holds_of_check` ([Cond](Cond.lean)) applies
`ball_encloses` to both sides of each comparison.

## Scope

A real power `rpow` returns an invalid ball; the other twenty constructors of
`CAS.Verified.Expr` are evaluated. SymLean has balls for rational powers
(`IntervalBalls.rpowRatBall`, [GridBallRpow](../Numerics/GridBallRpow.lean)), which could
evaluate `rpow a (rat p q)`. A maximum written with `maxE` is enclosed with up to three
times the radius of its arguments. Sine, cosine, arcsine and arccosine use exact rational
interval arithmetic.
-/

@[expose] public section

namespace CAS.Cert

open CAS.Numerics CAS.Verified

/-- The reciprocal of a ball that decides the sign of its numbers: `GridBall.inv` for positive
numbers, and `-(-a)⁻¹` otherwise, which is valid only for negative numbers. -/
def recip (P : ℕ) (a : GridBall) : GridBall :=
  Bool.rec (GridBall.neg (GridBall.inv P (GridBall.neg a))) (GridBall.inv P a)
    (GridBall.posCertain a)

/-- If `a` encloses the real `x`, then `recip P a` encloses `x⁻¹`. -/
theorem recip_encloses {P : ℕ} {a : GridBall} {x : ℝ} (ha : a.EnclosesReal P x) :
    (recip P a).EnclosesReal P x⁻¹ := by
  unfold recip
  cases GridBall.posCertain a
  · have := ha.neg.inv.neg
    rwa [inv_neg, neg_neg] at this
  · exact ha.inv

/-- The absolute value `|a|` as an expression: `√(a ^ 2)`, the form that SymLean's reifier
writes. -/
abbrev absE {ι : Type*} (a : Expr ι) : Expr ι :=
  CAS.Elaboration.RealExpression.DesugaredFunction.desugar .abs a

/-- `absE a` denotes `|a|`. -/
theorem eval_absE {ι : Type*} (ρ : ι → ℝ) (a : Expr ι) : (absE a).eval ρ = |a.eval ρ| := by
  simp [absE, CAS.Elaboration.RealExpression.DesugaredFunction.desugar, Real.sqrt_sq_eq_abs]

/-- The maximum of two expressions, `(a + b + |a - b|) / 2`. -/
def maxE {ι : Type*} (a b : Expr ι) : Expr ι :=
  .div (.add (.add a b) (absE (.sub a b))) (.nat 2)

/-- `maxE a b` denotes `max a b`. -/
theorem eval_maxE {ι : Type*} (ρ : ι → ℝ) (a b : Expr ι) :
    (maxE a b).eval ρ = max (a.eval ρ) (b.eval ρ) := by
  simp only [maxE, Expr.eval, eval_absE, Nat.cast_ofNat]
  rcases le_total (a.eval ρ) (b.eval ρ) with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]; ring

/-- The minimum of two expressions, `(a + b - |a - b|) / 2`. -/
def minE {ι : Type*} (a b : Expr ι) : Expr ι :=
  .div (.sub (.add a b) (absE (.sub a b))) (.nat 2)

/-- `minE a b` denotes `min a b`. -/
theorem eval_minE {ι : Type*} (ρ : ι → ℝ) (a b : Expr ι) :
    (minE a b).eval ρ = min (a.eval ρ) (b.eval ρ) := by
  simp only [minE, Expr.eval, eval_absE, Nat.cast_ofNat]
  rcases le_total (a.eval ρ) (b.eval ρ) with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring

/-- The ball of an expression at precision `P`, from the balls `benv` of its variables. The
square root of a square is the absolute value; a real power gives an invalid ball. -/
def ball {ι : Type*} (P : ℕ) (benv : ι → GridBall) : Expr ι → GridBall
  | .nat n => GridBall.ofNat P n
  | .int z => GridBall.ofFrac P (decide (z < 0)) z.natAbs 1
  | .rat num den => GridBall.ofFrac P (decide (num < 0)) num.natAbs den
  | .pi => GridBall.pi P
  | .e => GridBall.exp P (GridBall.ofNat P 1)
  | .var i => benv i
  | .add a b => GridBall.add (ball P benv a) (ball P benv b)
  | .mul a b => GridBall.mul P (ball P benv a) (ball P benv b)
  | .sub a b => GridBall.sub (ball P benv a) (ball P benv b)
  | .div a b => GridBall.mul P (ball P benv a) (recip P (ball P benv b))
  | .neg a => GridBall.neg (ball P benv a)
  | .pow a n => GridBall.pow P (ball P benv a) n
  | .sqrt (.pow a 2) => GridBall.abs (ball P benv a)
  | .sqrt a => GridBall.sqrt P (ball P benv a)
  | .exp a => GridBall.exp P (ball P benv a)
  | .log a => GridBall.log P (ball P benv a)
  | .atan a => GridBall.arctan P (ball P benv a)
  | .sin a => GridBall.sin P (ball P benv a)
  | .cos a => GridBall.cos P (ball P benv a)
  | .asin a => GridBall.arcsin P (ball P benv a)
  | .acos a => GridBall.arccos P (ball P benv a)
  | .rpow _ _ => GridBall.invalid

/-- **Soundness of the evaluator.** If the ball `benv i` encloses the real number `ρ i` for
every variable `i`, then `ball P benv expr` encloses the real value `expr.eval ρ` of the
expression, for every expression `expr` and every precision `P`.

This is the theorem between a computation on natural numbers and a statement about real
numbers: every test on balls of `CAS.Cert` goes through it. The proof is the induction over
`expr` with the soundness theorem of one ball operation per constructor. -/
theorem ball_encloses {ι : Type*} {P : ℕ} {benv : ι → GridBall} {ρ : ι → ℝ}
    (henv : ∀ i, (benv i).EnclosesReal P (ρ i)) (expr : Expr ι) :
    (ball P benv expr).EnclosesReal P (expr.eval ρ) := by
  fun_induction ball P benv expr with
  | case1 n => exact GridBall.enclosesReal_ofNat P n
  | case2 z => simpa using GridBall.enclosesReal_ofFrac P z 1
  | case3 num den => exact GridBall.enclosesReal_ofFrac P num den
  | case4 => exact GridBall.enclosesReal_pi P
  | case5 => simpa using (GridBall.enclosesReal_ofNat P 1).exp
  | case6 i => exact henv i
  | case7 a b iha ihb => exact iha.add ihb
  | case8 a b iha ihb => exact iha.mul ihb
  | case9 a b iha ihb => exact iha.sub ihb
  | case10 a b iha ihb => exact iha.mul (recip_encloses ihb)
  | case11 a iha => exact iha.neg
  | case12 a n iha => exact iha.pow n
  | case13 a iha =>
    -- The square root of a square is the absolute value.
    simpa [Real.sqrt_sq_eq_abs] using iha.abs
  | case14 a _ iha => exact iha.sqrt
  | case15 a iha => exact iha.exp
  | case16 a iha => exact iha.log
  | case17 a iha => exact iha.arctan
  | case18 a iha => exact iha.sin
  | case19 a iha => exact iha.cos
  | case20 a iha => exact iha.arcsin
  | case21 a iha => exact iha.arccos
  | case22 => exact GridBall.enclosesReal_of_not_ok rfl _

end CAS.Cert

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.GridBallReal
public import CAS.Numerics.GridBallSqrt
public import CAS.Numerics.GridBallExp
public import CAS.Numerics.GridBallLog
public import CAS.Numerics.GridBallAtan
public import CAS.Continuum.IntervalEval.Digits

/-!
# Elementary functions and `π` on single balls

## Motivation

SymLean encloses the square root, the exponential, the logarithm and the arctangent of an
interval by pairs of balls (`sqrtRangeBall`, `expRangeBall`, `logRangeBall`, `atanRangeBall`),
one ball for each end of an exact rational interval, and the sine, the cosine, the arcsine and
the arccosine by exact rational intervals (`DigitsEval.sin` and the others): the first two from
FloatLib's enclosures, the last two from the arctangent and the square root. A checker that
carries one ball per real number needs all of them as functions from a ball to a ball. Can the
existing functions be used as they are, with no new analysis?

## The idea

A ball is an interval with rational ends. Its two ends are balls of radius zero (`ends`), which
enclose the ends of that interval exactly, so every interval function of SymLean on pairs of
balls applies to them. Its result, a pair of balls for the ends of an interval that contains
the value, is turned back into one ball by `GridBall.hull` (`range`). A function on exact
rational intervals is applied to the interval of the ball, and the result is enclosed by the
hull of the balls of its two ends (`exact`). In both cases the soundness of the single-ball
function is the composition of existing theorems.

## Main results

For all balls, all precisions and all real numbers:

* `enclosesReal_range`: if the function `F` on pairs of balls, applied to the ends of `a`,
  encloses a rational interval that contains `y`, then `range F a` encloses `y`.
* `enclosesReal_exact`: if the function `F` on rational intervals maps the interval of `a` to an
  interval that contains `y`, then `exact P F a` encloses `y`.
* `EnclosesReal.sqrt`, `.exp`, `.arctan`, `.log`: `sqrt P a`, `exp P a`, `arctan P a` and
  `log P a` enclose `Real.sqrt x`, `Real.exp x`, `Real.arctan x` and `Real.log x` when `a`
  encloses `x`. The ball `log P a` is valid only when `a` decides that `x` is positive.
* `EnclosesReal.sin`, `.cos`, `.arcsin`, `.arccos`: the same for `Real.sin`, `Real.cos`,
  `Real.arcsin` and `Real.arccos`.
* `enclosesReal_pi`: `pi P` encloses `π`. The radius of `pi P` is about `10⁻²⁰ / 2` plus three
  grid units `2 ^ -P`, so it reaches twenty decimals from about 70 bits and never more.

## Relations

The first four theorems are `enclosesReal_range` applied to `sqrtRangeBall_encloses` with
`RationalInterval.sqrtRangeInterval_sound`, to `expRangeBall_encloses` with `expRangeWith_sound`,
to `atanRangeBall_encloses` with `atanRangeWith_sound`, and to `logRangeBall_encloses` with
`logRangeWith_sound`. The next four are `enclosesReal_exact` applied to `DigitsEval.sin_sound`,
`cos_sound`, `asin_sound` and `acos_sound` ([Digits](../Continuum/IntervalEval/Digits.lean)).
The first two rest on FloatLib's `containsReal_sinBounds` and `containsReal_cosBounds`. The
arcsine of an interval is taken at its two ends, since it is monotone: an end `q` inside
`(-1, 1)` gives the arctangent of `q / √(1 - q ^ 2)`, an end at or beyond `±1` gives `±π / 2`,
and a range bound is the fallback. The arccosine is `π / 2` minus the arcsine.
`enclosesReal_pi` is `enclosesReal_hull` at the twenty-decimal bounds
`RationalInterval.piLower_le_pi` and `pi_le_piUpper`. `CAS.Cert.ball_encloses` uses all of them.

## Scope

The enclosure of `π` has at most twenty decimals whatever the precision, since it comes from
`piInterval`; Machin's `piQuarterBalls` would give the full precision. The four functions that
go through exact rational intervals cost rational arithmetic in the kernel for each value. Real
powers have no single-ball form here; `IntervalBalls.rpowRatBall`
([GridBallRpow](GridBallRpow.lean)) gives powers with a rational exponent on pairs of balls. The
series parameters (`P / 2`, and `P / 4 + 8` for the trigonometric functions) are fixed and not
tuned.
-/

@[expose] public section

namespace CAS.Numerics.GridBall

open CAS.Continuum

/-- The two ends of a ball as balls of radius zero. -/
def ends (a : GridBall) : IntervalBalls :=
  ⟨⟨a.p, Nat.add a.n a.e, 0, a.ok⟩, ⟨Nat.add a.p a.e, a.n, 0, a.ok⟩⟩

/-- The lower end of a ball is at most its upper end. -/
theorem lo_le_hi (P : ℕ) (a : GridBall) : lo P a ≤ hi P a := by
  have : (0 : ℚ) ≤ a.e := Nat.cast_nonneg _
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- The exact rational interval between the two ends of a ball. -/
def interval (P : ℕ) (a : GridBall) : RationalInterval :=
  RationalInterval.ofBounds (lo P a) (hi P a) (lo_le_hi P a)

/-- The balls `ends a` enclose the ends of `interval P a` exactly. -/
theorem ends_encloses (P : ℕ) (a : GridBall) : (ends a).Encloses P (interval P a) := by
  have h2 : (2 : ℚ) ^ P ≠ 0 := by positivity
  constructor <;> intro _
  · change |lo P a * 2 ^ P - _| ≤ _
    rw [lo, div_mul_cancel₀ _ h2]
    simp only [ends, center, Nat.add_eq]
    push_cast
    rw [show (a.p : ℚ) - a.n - a.e - (a.p - (a.n + a.e)) = 0 by ring]
    simp
  · change |hi P a * 2 ^ P - _| ≤ _
    rw [hi, div_mul_cancel₀ _ h2]
    simp only [ends, center, Nat.add_eq]
    push_cast
    rw [show (a.p : ℚ) - a.n + a.e - (a.p + a.e - a.n) = 0 by ring]
    simp

/-- A real number of a valid ball lies in its interval. -/
theorem EnclosesReal.memReal_interval {P : ℕ} {a : GridBall} {x : ℝ} (hx : a.EnclosesReal P x)
    (hok : a.ok = true) : (interval P a).MemReal x :=
  ⟨hx.lo_le hok, hx.le_hi hok⟩

/-- If `b = true` implies that `a` encloses the real `x`, then `guard b a` encloses `x`. -/
theorem enclosesReal_guard {P : ℕ} {b : Bool} {a : GridBall} {x : ℝ}
    (h : b = true → a.ok = true → a.EnclosesReal P x) : (guard b a).EnclosesReal P x := by
  intro hok
  simp only [guard, Bool.and_eq_true] at hok
  exact h hok.2 hok.1 hok.1

/-- The single ball of an interval function `F` at a ball: `F` is applied to the two ends, and
the result is the `hull` of the two resulting balls. It is invalid when `a` is. -/
def range (F : IntervalBalls → IntervalBalls) (a : GridBall) : GridBall :=
  guard a.ok (hull (F (ends a)).lo (F (ends a)).hi)

/-- **Interval functions on single balls.** Let `a` be a ball and `y` a real number. If, when
`a` is valid, the pair of balls `F (ends a)` encloses a rational interval that contains `y`,
then the single ball `range F a` encloses `y`. This is the only step between the interval
functions of SymLean and their single-ball forms: the hull of two balls encloses everything
between a number of the first and a number of the second (`enclosesReal_hull`). -/
theorem enclosesReal_range {P : ℕ} {a : GridBall} {y : ℝ} {F : IntervalBalls → IntervalBalls}
    (h : a.ok = true → ∃ J : RationalInterval, (F (ends a)).Encloses P J ∧ J.MemReal y) :
    (range F a).EnclosesReal P y :=
  enclosesReal_guard fun hok _ ↦ by
    obtain ⟨J, hJ, hy⟩ := h hok
    exact enclosesReal_hull (enclosesReal_ratCast.mpr hJ.1) (enclosesReal_ratCast.mpr hJ.2)
      hy.1 hy.2

/-- The square root of a ball, to `P` bits. -/
def sqrt (P : ℕ) (a : GridBall) : GridBall := range (sqrtRangeBall P P) a

/-- If `a` encloses the real `x`, then `sqrt P a` encloses `Real.sqrt x`. -/
theorem EnclosesReal.sqrt {P : ℕ} {a : GridBall} {x : ℝ} (hx : a.EnclosesReal P x) :
    (GridBall.sqrt P a).EnclosesReal P (Real.sqrt x) :=
  enclosesReal_range fun hok ↦ ⟨_, sqrtRangeBall_encloses (ends_encloses P a),
    RationalInterval.sqrtRangeInterval_sound _ _ (hx.memReal_interval hok)⟩

/-- The exponential of a ball, at Taylor order `P / 2`. -/
def exp (P : ℕ) (a : GridBall) : GridBall :=
  range (IntervalBalls.expRangeBall P (Nat.div P 2)) a

/-- If `a` encloses the real `x`, then `exp P a` encloses `Real.exp x`. -/
theorem EnclosesReal.exp {P : ℕ} {a : GridBall} {x : ℝ} (hx : a.EnclosesReal P x) :
    (GridBall.exp P a).EnclosesReal P (Real.exp x) :=
  enclosesReal_range fun hok ↦ ⟨_, IntervalBalls.expRangeBall_encloses (ends_encloses P a),
    RationalInterval.expRangeWith_sound _ _ (hx.memReal_interval hok)⟩

/-- The arctangent of a ball, with series degree `P / 2`. -/
def arctan (P : ℕ) (a : GridBall) : GridBall :=
  range (IntervalBalls.atanRangeBall P (Nat.div P 2)) a

/-- If `a` encloses the real `x`, then `arctan P a` encloses `Real.arctan x`. -/
theorem EnclosesReal.arctan {P : ℕ} {a : GridBall} {x : ℝ} (hx : a.EnclosesReal P x) :
    (GridBall.arctan P a).EnclosesReal P (Real.arctan x) :=
  enclosesReal_range fun hok ↦ ⟨_, IntervalBalls.atanRangeBall_encloses (ends_encloses P a),
    RationalInterval.atanRangeWith_sound _ _ (hx.memReal_interval hok)⟩

/-- The logarithm of a ball, with a series of `P / 2` terms; invalid unless the ball decides
that its numbers are positive. -/
def log (P : ℕ) (a : GridBall) : GridBall :=
  guard (posCertain a) (range (IntervalBalls.logRangeBall P (Nat.div P 2)) a)

/-- If `a` encloses the real `x`, then `log P a` encloses `Real.log x`. -/
theorem EnclosesReal.log {P : ℕ} {a : GridBall} {x : ℝ} (hx : a.EnclosesReal P x) :
    (GridBall.log P a).EnclosesReal P (Real.log x) :=
  enclosesReal_guard fun hpos _ ↦ enclosesReal_range fun hok ↦
    have h : 0 < (interval P a).lo := GridBall.pos_of_posCertain (encloses_lo P a) hpos
    ⟨_, IntervalBalls.logRangeBall_encloses (ends_encloses P a) h,
      RationalInterval.logRangeWith_sound _ _ h (hx.memReal_interval hok)⟩

/-- A ball for `π`, the hull of the twenty-decimal bounds of `RationalInterval.piInterval`. -/
def pi (P : ℕ) : GridBall :=
  hull (ofFrac P false 314159265358979323846 100000000000000000000)
    (ofFrac P false 314159265358979323847 100000000000000000000)

/-- `pi P` encloses `π`. -/
theorem enclosesReal_pi (P : ℕ) : (pi P).EnclosesReal P Real.pi := by
  have hl := enclosesReal_ratCast.mpr
    (ofFrac_encloses P 314159265358979323846 100000000000000000000).1
  have hu := enclosesReal_ratCast.mpr
    (ofFrac_encloses P 314159265358979323847 100000000000000000000).1
  refine enclosesReal_hull hl hu ?_ ?_
  · have := RationalInterval.piLower_le_pi
    simpa [RationalInterval.piLower] using this
  · have := RationalInterval.pi_le_piUpper
    simpa [RationalInterval.piUpper] using this

/-! ### Functions on exact rational intervals -/

/-- The ball of an exact rational interval: the hull of the balls of its two ends. -/
def ofInterval (P : ℕ) (J : RationalInterval) : GridBall := hull (ofRat P J.lo) (ofRat P J.hi)

/-- If the real `y` lies in the rational interval `J`, then `ofInterval P J` encloses `y`. -/
theorem enclosesReal_ofInterval {P : ℕ} {J : RationalInterval} {y : ℝ} (hy : J.MemReal y) :
    (ofInterval P J).EnclosesReal P y :=
  enclosesReal_hull (enclosesReal_ratCast.mpr (ofRat_encloses P J.lo))
    (enclosesReal_ratCast.mpr (ofRat_encloses P J.hi)) hy.1 hy.2

/-- The single ball of a function `F` on exact rational intervals at a ball: `F` is applied to
the interval of the ball. It is invalid when `a` is. -/
def exact (P : ℕ) (F : RationalInterval → RationalInterval) (a : GridBall) : GridBall :=
  guard a.ok (ofInterval P (F (interval P a)))

/-- **Functions on rational intervals, on single balls.** If `a` encloses the real `x` and `F`
maps the interval of `a`, which then contains `x`, to an interval that contains `y`, then
`exact P F a` encloses `y`. -/
theorem enclosesReal_exact {P : ℕ} {a : GridBall} {x y : ℝ}
    {F : RationalInterval → RationalInterval} (hx : a.EnclosesReal P x)
    (h : (interval P a).MemReal x → (F (interval P a)).MemReal y) :
    (exact P F a).EnclosesReal P y :=
  enclosesReal_guard fun hok _ ↦ enclosesReal_ofInterval (h (hx.memReal_interval hok))

/-- The precision of the trigonometric enclosures at `P` bits: `P / 4 + 8` series terms. The
logarithm kernel of `DigitsEval` is not used here. -/
def trigPrecision (P : ℕ) : DigitsEval.Precision := ⟨P, Nat.add (Nat.div P 4) 8, P⟩

/-- The sine of a ball, from FloatLib's enclosure of the sine on a rational interval. -/
def sin (P : ℕ) (a : GridBall) : GridBall := exact P (DigitsEval.sin (trigPrecision P)) a

/-- If `a` encloses the real `x`, then `sin P a` encloses `Real.sin x`. -/
theorem EnclosesReal.sin {P : ℕ} {a : GridBall} {x : ℝ} (hx : a.EnclosesReal P x) :
    (GridBall.sin P a).EnclosesReal P (Real.sin x) :=
  enclosesReal_exact hx (DigitsEval.sin_sound _)

/-- The cosine of a ball, from FloatLib's enclosure of the cosine on a rational interval. -/
def cos (P : ℕ) (a : GridBall) : GridBall := exact P (DigitsEval.cos (trigPrecision P)) a

/-- If `a` encloses the real `x`, then `cos P a` encloses `Real.cos x`. -/
theorem EnclosesReal.cos {P : ℕ} {a : GridBall} {x : ℝ} (hx : a.EnclosesReal P x) :
    (GridBall.cos P a).EnclosesReal P (Real.cos x) :=
  enclosesReal_exact hx (DigitsEval.cos_sound _)

/-- The arcsine of a ball. -/
def arcsin (P : ℕ) (a : GridBall) : GridBall := exact P (DigitsEval.asin (trigPrecision P)) a

/-- If `a` encloses the real `x`, then `arcsin P a` encloses `Real.arcsin x`. -/
theorem EnclosesReal.arcsin {P : ℕ} {a : GridBall} {x : ℝ} (hx : a.EnclosesReal P x) :
    (GridBall.arcsin P a).EnclosesReal P (Real.arcsin x) :=
  enclosesReal_exact hx (DigitsEval.asin_sound _)

/-- The arccosine of a ball. -/
def arccos (P : ℕ) (a : GridBall) : GridBall := exact P (DigitsEval.acos (trigPrecision P)) a

/-- If `a` encloses the real `x`, then `arccos P a` encloses `Real.arccos x`. -/
theorem EnclosesReal.arccos {P : ℕ} {a : GridBall} {x : ℝ} (hx : a.EnclosesReal P x) :
    (GridBall.arccos P a).EnclosesReal P (Real.arccos x) :=
  enclosesReal_exact hx (DigitsEval.acos_sound _)

end CAS.Numerics.GridBall

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Basic
import CAS.Continuum.Interval.Rational.FiniteSum

/-!
# Rational interval arithmetic through FloatLib

Addition, negation, subtraction, multiplication, natural powers and reciprocals of rational
intervals are FloatLib's exact rational interval operations with the endpoint-order proof of
`RationalInterval` attached. They never round and never fail. The reciprocal `invPositive` and
the quotient `divPositive` require a denominator with positive lower endpoint.

## Main results

* `add_sound`, `neg_sound`, `sub_sound`, `mul_sound`, `powNat_sound`: the inclusion property of
  interval arithmetic, for example `x ∈ I` and `y ∈ J` imply `x * y ∈ I.mul J`.
* `invPositive_sound`, `divPositive_sound`: the same for reciprocals and quotients by a
  denominator with positive lower endpoint.
* `add_lo`, `mul_lo`, `invPositive_hi` and the other endpoint `simp` lemmas.

## Implementation notes

The endpoint formulas are the classical ones of Rump, (5.4) and (5.5): endpoint sums and
differences for `add` and `sub`, and the minimum and maximum of the four endpoint products for
`mul`. The operations are those of `FloatLib.Numerics.Interval.Exact`, written with the kernel
rational functions of FloatLib, and FloatLib states their endpoints (`Exact.add_lo`,
`Exact.mul_hi` and the others) and proves their inclusion theorems (`Exact.containsReal_add` and
the others). We translate its `ContainsReal` into `MemReal`, and each definition takes its order
proof from the inclusion theorem at the lower endpoints of its inputs.

Three operations keep a definition that proofs about balls unfold. `powNat` is FloatLib's
`powBounds`, which is `Exact.powNat` at `ℚ` (`Exact.powBounds_eq`); `CAS.Numerics.IntervalBalls`
reads its endpoints from `powBounds`. `divPositive I J` is the product of `I` with the reciprocal
of `J`, the same interval as `Exact.div`, and `scaleNonneg q I` is the product with the singleton
`[q, q]`, the same interval as `Exact.scaleNonneg` for `0 ≤ q`.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, <https://github.com/lean-dojo/FloatLib>.
* Ramon E. Moore, R. Baker Kearfott and Michael J. Cloud, *Introduction to Interval Analysis*,
  SIAM, Philadelphia, 2009, <https://doi.org/10.1137/1.9780898717716>. Chapter 2, The Interval
  Number System.
* Siegfried M. Rump, "Verification methods: Rigorous results using floating-point arithmetic",
  *Acta Numerica* 19 (2010), pp. 287-449, <https://doi.org/10.1017/S096249291000005X>.
  Section 5.1 for the operations, Section 5.5 for the inclusion property (5.16).
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open FloatLib.Numerics.Interval

/-- Interval addition, FloatLib's exact sum. -/
def add (I J : RationalInterval) : RationalInterval :=
  ofFloatLib (Exact.add I.toFloatLib J.toFloatLib)
    (ordered_of_containsReal (Exact.containsReal_add I.containsReal_lo J.containsReal_lo))

/-- Interval negation, FloatLib's exact negation. -/
def neg (I : RationalInterval) : RationalInterval :=
  ofFloatLib (Exact.neg I.toFloatLib)
    (ordered_of_containsReal (Exact.containsReal_neg I.containsReal_lo))

/-- Interval subtraction, FloatLib's exact difference. -/
def sub (I J : RationalInterval) : RationalInterval :=
  ofFloatLib (Exact.sub I.toFloatLib J.toFloatLib)
    (ordered_of_containsReal (Exact.containsReal_sub I.containsReal_lo J.containsReal_lo))

/-- Sharp four-corner multiplication, FloatLib's exact product. -/
@[irreducible] def mul (I J : RationalInterval) : RationalInterval :=
  ofFloatLib (Exact.mul I.toFloatLib J.toFloatLib)
    (ordered_of_containsReal (Exact.containsReal_mul I.containsReal_lo J.containsReal_lo))

/-- Natural powers use FloatLib's sharp odd/even endpoint bounds and binary powering. -/
def powNat (I : RationalInterval) (k : Nat) : RationalInterval :=
  ofFloatLib (powBounds I.toFloatLib k) (by
    rw [Exact.powBounds_eq]
    exact ordered_of_containsReal (Exact.containsReal_powNat k I.containsReal_lo))

/-- The maximum absolute magnitude of a member, FloatLib's `max |I.lo| |I.hi|`. -/
def absMax (I : RationalInterval) : ℚ :=
  Exact.absMax I.toFloatLib

/-- `absMax I = max |I.lo| |I.hi|`. -/
theorem absMax_eq_max (I : RationalInterval) : I.absMax = max |I.lo| |I.hi| :=
  Exact.absMax_eq I.toFloatLib

/-- Maximum absolute endpoint magnitude is nonnegative. -/
theorem absMax_nonneg (I : RationalInterval) : 0 ≤ I.absMax :=
  Exact.absMax_nonneg I.toFloatLib

/-- Reciprocal of a positive interval, FloatLib's exact reciprocal. -/
def invPositive (J : RationalInterval) (hJ : 0 < J.lo) : RationalInterval :=
  ofFloatLib (Exact.inv J.toFloatLib)
    (ordered_of_containsReal (Exact.containsReal_inv (Or.inr hJ) J.containsReal_lo))

/-- Sharp division by a positive interval, using FloatLib multiplication and reciprocal. -/
def divPositive (I J : RationalInterval) (hJ : 0 < J.lo) : RationalInterval :=
  I.mul (J.invPositive hJ)

/-- Divide when the denominator has a positive lower endpoint; otherwise return zero.
The fallback keeps finite evaluators total. A real quotient enclosure still requires
the positive-denominator hypothesis in `divPositiveOrZero_sound`. -/
def divPositiveOrZero (I J : RationalInterval) : RationalInterval :=
  if h : 0 < J.lo then I.divPositive J h else const 0

/-- Nonnegative scaling is FloatLib multiplication by a singleton interval. -/
def scaleNonneg (q : ℚ) (_hq : 0 ≤ q) (I : RationalInterval) : RationalInterval :=
  (const q).mul I

/-! ## Endpoint formulas

These simp lemmas give the endpoints of each operation without unfolding the FloatLib adapters.
For positive division, `simp [divPositive]` combines the multiplication and reciprocal rules.
The separate `absMax_eq_max` theorem exposes the maximum absolute endpoint when needed.
-/

/-- The lower endpoint of a sum is the sum of the lower endpoints. -/
@[simp] theorem add_lo (I J : RationalInterval) : (I.add J).lo = I.lo + J.lo :=
  Exact.add_lo I.toFloatLib J.toFloatLib
/-- The upper endpoint of a sum is the sum of the upper endpoints. -/
@[simp] theorem add_hi (I J : RationalInterval) : (I.add J).hi = I.hi + J.hi :=
  Exact.add_hi I.toFloatLib J.toFloatLib
/-- The lower endpoint after negation is the negated upper endpoint. -/
@[simp] theorem neg_lo (I : RationalInterval) : I.neg.lo = -I.hi :=
  Exact.neg_lo I.toFloatLib
/-- The upper endpoint after negation is the negated lower endpoint. -/
@[simp] theorem neg_hi (I : RationalInterval) : I.neg.hi = -I.lo :=
  Exact.neg_hi I.toFloatLib
/-- Subtraction subtracts the upper endpoint from the lower endpoint. -/
@[simp] theorem sub_lo (I J : RationalInterval) : (I.sub J).lo = I.lo - J.hi :=
  Exact.sub_lo I.toFloatLib J.toFloatLib
/-- Subtraction subtracts the lower endpoint from the upper endpoint. -/
@[simp] theorem sub_hi (I J : RationalInterval) : (I.sub J).hi = I.hi - J.lo :=
  Exact.sub_hi I.toFloatLib J.toFloatLib

/-- The lower product endpoint is the minimum of the four endpoint products. -/
@[simp] theorem mul_lo (I J : RationalInterval) :
    (I.mul J).lo = min (min (I.lo * J.lo) (I.lo * J.hi))
      (min (I.hi * J.lo) (I.hi * J.hi)) := by
  unfold mul
  exact Exact.mul_lo I.toFloatLib J.toFloatLib

/-- The upper product endpoint is the maximum of the four endpoint products. -/
@[simp] theorem mul_hi (I J : RationalInterval) :
    (I.mul J).hi = max (max (I.lo * J.lo) (I.lo * J.hi))
      (max (I.hi * J.lo) (I.hi * J.hi)) := by
  unfold mul
  exact Exact.mul_hi I.toFloatLib J.toFloatLib

/-- The lower reciprocal endpoint is the reciprocal of the positive upper endpoint. -/
@[simp] theorem invPositive_lo (J : RationalInterval) (hJ : 0 < J.lo) :
    (J.invPositive hJ).lo = 1 / J.hi :=
  (Exact.inv_lo J.toFloatLib).trans (one_div J.hi).symm

/-- The upper reciprocal endpoint is the reciprocal of the positive lower endpoint. -/
@[simp] theorem invPositive_hi (J : RationalInterval) (hJ : 0 < J.lo) :
    (J.invPositive hJ).hi = 1 / J.lo :=
  (Exact.inv_hi J.toFloatLib).trans (one_div J.lo).symm

/-- Nonnegative scaling multiplies the lower endpoint by the scale. -/
@[simp] theorem scaleNonneg_lo (q : ℚ) (hq : 0 ≤ q) (I : RationalInterval) :
    (I.scaleNonneg q hq).lo = q * I.lo := by
  simp [scaleNonneg, min_eq_left (mul_le_mul_of_nonneg_left I.hle hq)]

/-- Nonnegative scaling multiplies the upper endpoint by the scale. -/
@[simp] theorem scaleNonneg_hi (q : ℚ) (hq : 0 ≤ q) (I : RationalInterval) :
    (I.scaleNonneg q hq).hi = q * I.hi := by
  simp [scaleNonneg, max_eq_right (mul_le_mul_of_nonneg_left I.hle hq)]

/-- Addition of singleton intervals is exact. -/
@[simp] theorem const_add_const (a b : ℚ) :
    (const a).add (const b) = const (a + b) := by
  ext <;> simp

/-- Negation of a singleton interval is exact. -/
@[simp] theorem neg_const (a : ℚ) : (const a).neg = const (-a) := by
  ext <;> simp

/-- Subtraction of singleton intervals is exact. -/
@[simp] theorem const_sub_const (a b : ℚ) :
    (const a).sub (const b) = const (a - b) := by
  ext <;> simp

/-- Multiplication of singleton intervals is exact. -/
@[simp] theorem const_mul_const (a b : ℚ) :
    (const a).mul (const b) = const (a * b) := by
  ext <;> simp

/-! ## Real containment from FloatLib -/

/-- Addition contains the sum of any two contained real values. -/
theorem add_sound {I J : RationalInterval} {x y : ℝ}
    (hx : I.MemReal x) (hy : J.MemReal y) :
    (I.add J).MemReal (x + y) :=
  ((I.add J).toFloatLib_containsReal_iff _).mp (Exact.containsReal_add
    ((I.toFloatLib_containsReal_iff _).mpr hx) ((J.toFloatLib_containsReal_iff _).mpr hy))

/-- Negation contains the negation of every contained real value. -/
theorem neg_sound {I : RationalInterval} {x : ℝ}
    (hx : I.MemReal x) : I.neg.MemReal (-x) :=
  (I.neg.toFloatLib_containsReal_iff _).mp
    (Exact.containsReal_neg ((I.toFloatLib_containsReal_iff _).mpr hx))

/-- Subtraction contains the difference of any two contained real values. -/
theorem sub_sound {I J : RationalInterval} {x y : ℝ}
    (hx : I.MemReal x) (hy : J.MemReal y) :
    (I.sub J).MemReal (x - y) :=
  ((I.sub J).toFloatLib_containsReal_iff _).mp (Exact.containsReal_sub
    ((I.toFloatLib_containsReal_iff _).mpr hx) ((J.toFloatLib_containsReal_iff _).mpr hy))

/-- Multiplication contains the product of any two contained real values. -/
theorem mul_sound {I J : RationalInterval} {x y : ℝ}
    (hx : I.MemReal x) (hy : J.MemReal y) :
    (I.mul J).MemReal (x * y) := by
  rw [← toFloatLib_containsReal_iff]
  unfold mul
  exact Exact.containsReal_mul
    ((I.toFloatLib_containsReal_iff _).mpr hx) ((J.toFloatLib_containsReal_iff _).mpr hy)

/-- Natural powers contain the corresponding real powers. -/
theorem powNat_sound {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) (k : Nat) :
    (I.powNat k).MemReal (x ^ k) := by
  rw [← toFloatLib_containsReal_iff]
  change (powBounds I.toFloatLib k).ContainsReal some (x ^ k)
  rw [Exact.powBounds_eq]
  exact Exact.containsReal_powNat k ((I.toFloatLib_containsReal_iff _).mpr hx)

/-- FloatLib's absolute bound bounds the magnitude of every real member. -/
theorem abs_le_absMax {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    |x| ≤ (I.absMax : ℝ) :=
  Exact.abs_le_absMax ((I.toFloatLib_containsReal_iff _).mpr hx)

/-- The reciprocal of a positive interval contains every reciprocal value. -/
theorem invPositive_sound {J : RationalInterval} (hJ : 0 < J.lo) {y : ℝ}
    (hy : J.MemReal y) : (J.invPositive hJ).MemReal y⁻¹ :=
  ((J.invPositive hJ).toFloatLib_containsReal_iff _).mp
    (Exact.containsReal_inv (Or.inr hJ) ((J.toFloatLib_containsReal_iff _).mpr hy))

/-- Positive-denominator interval division contains the real quotient. -/
theorem divPositive_sound {I J : RationalInterval} (hJ : 0 < J.lo)
    {x y : ℝ} (hx : I.MemReal x) (hy : J.MemReal y) :
    (I.divPositive J hJ).MemReal (x / y) := by
  simpa only [divPositive, div_eq_mul_inv] using mul_sound hx (invPositive_sound hJ hy)

/-- A checked positive denominator validates the total division evaluator. -/
theorem divPositiveOrZero_sound {I J : RationalInterval} (hJ : 0 < J.lo)
    {x y : ℝ} (hx : I.MemReal x) (hy : J.MemReal y) :
    (I.divPositiveOrZero J).MemReal (x / y) := by
  simpa only [divPositiveOrZero, dite_eq_left hJ] using divPositive_sound hJ hx hy

/-- Nonnegative scaling contains the scaled value of every interval member. -/
theorem scaleNonneg_sound {I : RationalInterval} {q : ℚ} (hq : 0 ≤ q) {x : ℝ}
    (hx : I.MemReal x) : (I.scaleNonneg q hq).MemReal ((q : ℝ) * x) :=
  mul_sound (memReal_const q) hx

end RationalInterval
end CAS.Continuum

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.Proof
public import FloatLib.Numerics.Enclosure.Interval.ExactProof
public import FloatLib.Numerics.Enclosure.Trigonometric.AtanProof
public import CAS.Continuum.IntervalBackend

/-!
# Ordered FloatLib intervals for CEGA

CEGA uses FloatLib intervals with rational endpoints. `RationalInterval` adds an
endpoint-order proof, so that every interval has a midpoint and a nonnegative radius, which
refinement and quadrature use. Arithmetic and elementary-function enclosures are FloatLib's.
`MemReal I x` is the statement `I.lo ≤ x ∧ x ≤ I.hi` over `ℝ` used in the certificates.

## Main definitions

* `RationalInterval`, `MemReal`, `instRealIntervalBackend`: the representation, real
  membership, and the `RealIntervalBackend` instance.
* `const`, `ofBounds`, `hull`, `rationalHull`: singletons, intervals from ordered endpoints,
  the hull of two intervals, and a rational interval with denominator `d` around a real interval.
* `center`, `radius`, `midpointApproxCert`: midpoint data and the approximation certificate that
  replaces an enclosed function by the midpoint with error the radius.
* `negOneOne`, `piInterval`: the interval `[-1, 1]` and a twenty-decimal enclosure of `π`.

## Main results

* `ordered_of_containsReal`, `containsReal_lo`: an interval with a real member has ordered
  endpoints, and the lower endpoint of a rational interval is such a member.
* `piInterval_sound`: `π ∈ piInterval`. Four times FloatLib's degree-24 enclosure of `π / 4` lies
  inside the fixed bracket, and the rational endpoint comparisons are checked by the kernel.

The arithmetic operations and their soundness theorems are in
`CAS.Continuum.Interval.Rational.Arithmetic`.

## Implementation notes

The hull and the arithmetic operations are FloatLib's exact operations on `Interval ℚ`, those of
`FloatLib.Numerics.Interval.Exact`, which never round and never fail, and the outward roundings
of `CAS.Continuum.Interval.Rational.DyadicHull` and `CAS.Continuum.Interval.Rational.RelativeHull`
are FloatLib's roundings to binary grids. FloatLib proves that each operation contains the real
result for all real members of its inputs, so the order proof of a result can come from that
theorem at the lower endpoints of the inputs (`ordered_of_containsReal`, `containsReal_lo`), and
an operation lifts to `RationalInterval` without reasoning about its endpoints. The endpoint
lemmas, such as `hull_lo`, are FloatLib's endpoint equations. The fixed bracket of `π` has far
shorter endpoints than FloatLib's series enclosure, which keeps later computations with it small.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, <https://github.com/lean-dojo/FloatLib>.
-/

@[expose] public section

namespace CAS.Continuum

open CAS.Certificate

/--
A FloatLib interval with ordered rational endpoints.

The endpoint-order proof is the only well-formedness invariant.
-/
structure RationalInterval extends FloatLib.Numerics.Interval ℚ where
  /-- Endpoint-order invariant. -/
  hle : lo ≤ hi
deriving DecidableEq, Repr

namespace RationalInterval

/-- The interval passed directly to FloatLib's arithmetic and enclosure routines. -/
abbrev toFloatLib (I : RationalInterval) : FloatLib.Numerics.Interval ℚ :=
  I.toInterval

/-- Attach the endpoint-order proof required by CEGA to a FloatLib interval. -/
def ofFloatLib (I : FloatLib.Numerics.Interval ℚ) (h : I.lo ≤ I.hi) :
    RationalInterval :=
  { toInterval := I, hle := h }

/--
Real membership in a rational interval.

The endpoints are cast to `ℝ` because CEGA relations describe real-valued
functions.
-/
def MemReal (I : RationalInterval) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

/-- FloatLib's real containment is exactly the endpoint predicate used by CEGA. -/
theorem toFloatLib_containsReal_iff (I : RationalInterval) (x : ℝ) :
    I.toFloatLib.ContainsReal some x ↔ I.MemReal x :=
  FloatLib.Numerics.Interval.containsReal_some_iff _ _

/-- Containing a real value certifies that a FloatLib interval has ordered endpoints. -/
theorem ordered_of_containsReal {I : FloatLib.Numerics.Interval ℚ} {x : ℝ}
    (h : I.ContainsReal some x) : I.lo ≤ I.hi := by
  have hx := (FloatLib.Numerics.Interval.containsReal_some_iff I x).mp h
  exact_mod_cast hx.1.trans hx.2

/-- Attaching the order proof preserves FloatLib's real containment. -/
@[simp] theorem memReal_ofFloatLib_iff (I : FloatLib.Numerics.Interval ℚ)
    (h : I.lo ≤ I.hi) (x : ℝ) :
    (ofFloatLib I h).MemReal x ↔ I.ContainsReal some x :=
  (FloatLib.Numerics.Interval.containsReal_some_iff I x).symm

/-- The lower endpoint belongs to its rational interval. -/
@[simp] theorem lo_memReal (I : RationalInterval) : I.MemReal (I.lo : ℝ) := by
  exact ⟨le_rfl, by exact_mod_cast I.hle⟩

/-- The upper endpoint belongs to its rational interval. -/
@[simp] theorem hi_memReal (I : RationalInterval) : I.MemReal (I.hi : ℝ) := by
  exact ⟨by exact_mod_cast I.hle, le_rfl⟩

/-- FloatLib reads the lower endpoint of a rational interval as a real member of it. -/
theorem containsReal_lo (I : RationalInterval) : I.toFloatLib.ContainsReal some (I.lo : ℝ) :=
  (I.toFloatLib_containsReal_iff _).mpr I.lo_memReal

/-- The exact rational interval implementation of `RealIntervalBackend`. -/
@[reducible] instance instRealIntervalBackend : RealIntervalBackend RationalInterval where
  lo I := I.lo
  hi I := I.hi
  MemReal := MemReal
  lower_mem h := h.1
  upper_mem h := h.2

/-- The generic backend lower endpoint is the real cast of the rational lower endpoint. -/
@[simp] theorem realIntervalBackend_lo (I : RationalInterval) :
    RealIntervalBackend.lo I = (I.lo : ℝ) :=
  rfl

/-- The generic backend upper endpoint is the real cast of the rational upper endpoint. -/
@[simp] theorem realIntervalBackend_hi (I : RationalInterval) :
    RealIntervalBackend.hi I = (I.hi : ℝ) :=
  rfl

/-- Generic backend membership specializes to rational-interval real membership. -/
@[simp] theorem realIntervalBackend_memReal (I : RationalInterval) (x : ℝ) :
    RealIntervalBackend.MemReal I x ↔ I.MemReal x :=
  Iff.rfl

/-! ## Constructors and hulls -/

/-- The singleton interval `{q}`. -/
def const (q : ℚ) : RationalInterval where
  toInterval := FloatLib.Numerics.Interval.point q
  hle := le_rfl

/-- The lower endpoint of a singleton is its value. -/
@[simp] theorem const_lo (q : ℚ) : (const q).lo = q := rfl

/-- The upper endpoint of a singleton is its value. -/
@[simp] theorem const_hi (q : ℚ) : (const q).hi = q := rfl

/-- The singleton interval contains the real cast of its endpoint. -/
@[simp] theorem memReal_const (q : ℚ) : (const q).MemReal (q : ℝ) :=
  ⟨by simp, by simp⟩

/-- The closed rational interval with the supplied ordered endpoints. -/
def ofBounds (a b : ℚ) (hab : a ≤ b) : RationalInterval where
  lo := a
  hi := b
  hle := hab

/-- The smallest endpointwise rational interval containing `I` and `J`, FloatLib's exact hull
`[min I.lo J.lo, max I.hi J.hi]`. -/
def hull (I J : RationalInterval) : RationalInterval :=
  ofFloatLib (FloatLib.Numerics.Interval.Exact.hull I.toFloatLib J.toFloatLib)
    (ordered_of_containsReal
      (FloatLib.Numerics.Interval.Exact.containsReal_hull (Or.inl I.containsReal_lo)))

/-- FloatLib's hull selects the smaller lower endpoint. -/
@[simp] theorem hull_lo (I J : RationalInterval) :
    (I.hull J).lo = min I.lo J.lo :=
  FloatLib.Numerics.Interval.Exact.hull_lo I.toFloatLib J.toFloatLib

/-- FloatLib's hull selects the larger upper endpoint. -/
@[simp] theorem hull_hi (I J : RationalInterval) :
    (I.hull J).hi = max I.hi J.hi :=
  FloatLib.Numerics.Interval.Exact.hull_hi I.toFloatLib J.toFloatLib

/-- Every real point of the left interval belongs to the binary hull. -/
theorem memReal_hull_left {I J : RationalInterval} {x : ℝ}
    (hx : I.MemReal x) : (I.hull J).MemReal x :=
  ((I.hull J).toFloatLib_containsReal_iff x).mp
    (FloatLib.Numerics.Interval.Exact.containsReal_hull
      (Or.inl ((I.toFloatLib_containsReal_iff x).mpr hx)))

/-- Every real point of the right interval belongs to the binary hull. -/
theorem memReal_hull_right {I J : RationalInterval} {x : ℝ}
    (hx : J.MemReal x) : (I.hull J).MemReal x :=
  ((I.hull J).toFloatLib_containsReal_iff x).mp
    (FloatLib.Numerics.Interval.Exact.containsReal_hull
      (Or.inr ((J.toFloatLib_containsReal_iff x).mpr hx)))

/-- Real points between rational endpoints belong to `ofBounds`. -/
theorem memReal_ofBounds {a b : ℚ} (hab : a ≤ b)
    {x : ℝ} (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ)) :
    (ofBounds a b hab).MemReal x := by
  simpa [ofBounds, MemReal] using hx

/--
A fixed-denominator rational interval containing an arbitrary ordered real interval.

For a positive denominator `d`, the endpoints are `⌊d * a⌋ / d` and `⌈d * b⌉ / d`. Each
endpoint overshoots its real target by less than `1 / d` unless it is exact.
-/
noncomputable def rationalHull (d : ℕ) (hd : 0 < d)
    (a b : ℝ) (hab : a ≤ b) : RationalInterval where
  lo := (⌊(d : ℝ) * a⌋ : ℤ) / (d : ℚ)
  hi := (⌈(d : ℝ) * b⌉ : ℤ) / (d : ℚ)
  hle := by
    apply div_le_div_of_nonneg_right
    · exact_mod_cast
        ((Int.floor_le ((d : ℝ) * a)).trans
          ((mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg d)).trans
            (Int.le_ceil ((d : ℝ) * b))))
    · exact_mod_cast hd.le

/-- Every point of `[a, b]` lies in `rationalHull d hd a b hab`. -/
theorem memReal_rationalHull {d : ℕ} (hd : 0 < d)
    {a b x : ℝ} (hab : a ≤ b) (hx : x ∈ Set.Icc a b) :
    (rationalHull d hd a b hab).MemReal x := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  simp only [rationalHull, MemReal, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast,
    div_le_iff₀ hdR, le_div_iff₀ hdR]
  constructor
  · linarith [Int.floor_le ((d : ℝ) * a), mul_le_mul_of_nonneg_left hx.1 hdR.le]
  · linarith [Int.le_ceil ((d : ℝ) * b), mul_le_mul_of_nonneg_left hx.2 hdR.le]

/-! ## Midpoint data -/

/-- Midpoint of a rational interval. -/
def center (I : RationalInterval) : ℚ :=
  (I.lo + I.hi) / 2

/-- The rational midpoint, cast to a real, belongs to its closed interval. -/
theorem center_memReal (I : RationalInterval) : I.MemReal (I.center : ℝ) := by
  have h : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.hle
  constructor <;> simp only [center] <;> push_cast <;> linarith

/-- Radius of a rational interval around `center`. -/
def radius (I : RationalInterval) : ℚ :=
  (I.hi - I.lo) / 2

/-- The rational interval radius is nonnegative. -/
theorem radius_nonneg (I : RationalInterval) : 0 ≤ I.radius :=
  div_nonneg (sub_nonneg.mpr I.hle) zero_le_two

/-- The midpoint minus the radius is the lower endpoint. -/
theorem center_sub_radius_eq_lo (I : RationalInterval) :
    I.center - I.radius = I.lo := by
  unfold center radius
  ring

/-- The midpoint plus the radius is the upper endpoint. -/
theorem center_add_radius_eq_hi (I : RationalInterval) :
    I.center + I.radius = I.hi := by
  unfold center radius
  ring

/--
Interval containment gives a CEGA approximation by the interval midpoint.

This is the checked form of replacing an interval by its midpoint with the radius as a uniform
error budget.
-/
noncomputable def midpointApproxCert {α : Type*} {f : α → ℝ} {s : Set α}
    (I : RationalInterval) (h : ∀ x, x ∈ s → I.MemReal (f x)) :
    ApproxCert α ℝ s :=
  RealIntervalBackend.approxCertAroundOfMemRealLe
    (ι := RationalInterval) I (I.center : ℝ) (I.radius : ℝ)
    (by
      change (I.center : ℝ) - (I.radius : ℝ) ≤ (I.lo : ℝ)
      rw [← Rat.cast_sub, I.center_sub_radius_eq_lo])
    (by
      change (I.hi : ℝ) ≤ (I.center : ℝ) + (I.radius : ℝ)
      rw [← Rat.cast_add, I.center_add_radius_eq_hi])
    h

/-! ## Built-in constant ranges -/

/-- The universal trigonometric range interval `[-1, 1]`. -/
def negOneOne : RationalInterval where
  lo := -1
  hi := 1
  hle := by norm_num

/-- Twenty-decimal rational lower bound for `π`, certified by FloatLib's Machin enclosure. -/
def piLower : ℚ := 314159265358979323846 / 100000000000000000000

/-- Twenty-decimal rational upper bound for `π`, certified by FloatLib's Machin enclosure. -/
def piUpper : ℚ := 314159265358979323847 / 100000000000000000000

/-- The shared exact-rational enclosure for `π`, of width `10⁻²⁰`. -/
def piInterval : RationalInterval where
  lo := piLower
  hi := piUpper
  hle := by norm_num [piLower, piUpper]

/-- `piLower ≤ π`. -/
theorem piLower_le_pi : (piLower : ℝ) ≤ Real.pi := by
  have hlo : piLower ≤ 4 * (FloatLib.Numerics.Enclosure.piQuarter 24).lo := by decide +kernel
  have hloR : (piLower : ℝ) ≤ 4 * ((FloatLib.Numerics.Enclosure.piQuarter 24).lo : ℝ) := by
    exact_mod_cast hlo
  linarith [(FloatLib.Numerics.Enclosure.contains_piQuarter 24).1]

/-- `π ≤ piUpper`. -/
theorem pi_le_piUpper : Real.pi ≤ (piUpper : ℝ) := by
  have hhi : 4 * (FloatLib.Numerics.Enclosure.piQuarter 24).hi ≤ piUpper := by decide +kernel
  have hhiR : 4 * ((FloatLib.Numerics.Enclosure.piQuarter 24).hi : ℝ) ≤ (piUpper : ℝ) := by
    exact_mod_cast hhi
  linarith [(FloatLib.Numerics.Enclosure.contains_piQuarter 24).2]

/-- `piInterval` contains `π`. -/
theorem piInterval_sound : piInterval.MemReal Real.pi := by
  simpa [piInterval, MemReal] using And.intro piLower_le_pi pi_le_piUpper

end RationalInterval

end CAS.Continuum

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Certificate.Atlas.Approximation
public import CAS.Certificate.WeightedResidual
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Certificate rules on the unit interval

## Motivation

The modules under `CAS/Certificate` have rules that build a certificate from certificates. The
tactics and commands call some of them (`weaken`, `restrict`, `replaceRhs`, `replaceFn` and
others), and 39 have no caller in the library. What does each of these 39 compute on a problem
small enough to check by hand?

## The idea

A certificate is a function, some numbers and a proof that they fit: an enclosure
`lo ≤ f ≤ hi`, an upper bound `f ≤ c`, an approximation `|f - g| ≤ ε` or a residual bound
`|r| ≤ ε` on a set. Here the set is always an interval, called a patch, and `ε` is called the
budget. A rule takes certificates and returns a certificate whose numbers are computed from
theirs.

Three functions on `[0, 1]` are enough: the hat functions `x` and `1 - x`, and their product,
the bubble `x (1 - x)`. Its largest value is `1/4`, since `x (1 - x) = 1/4 - (x - 1/2) ^ 2`.
One enclosure is proved directly: on a patch `[a, b]` the function `x` takes values in
`[a, b]`. Every other certificate comes out of a rule. The certificates are built once, on a
patch `[a, b]` with symbolic endpoints. Each example then puts in the halves `[0, 1/2]` and
`[1/2, 1]`, the quarters, or one point, and evaluates the numbers.

* Interval arithmetic. Subtraction gives `1 - x ∈ [1 - b, 1 - a]`, and the product rule gives
  `x (1 - x) ∈ [a (1 - b), b (1 - a)]`. On `[0, 1]` the upper bound is `1`. On the left half it
  is `1/2`, and from the two quarters of the left half it is `3/8`. The four quarters give
  `3/8` on `[0, 1]`. The rules do not see that both factors depend on the same `x`. A finer
  cover makes up for it.
* Approximation. Each hat is within `1/2` of the constant `1/2`. With the factor `1 - x` frozen
  at `1/2`, the product rule compares the bubble with `x / 2`. The budget is
  `max |a| |b| / 2`: `1/4` on the left half and `1/2` on the right half. A glued certificate
  keeps the larger budget.
* Residuals. The defect `x + (1 - x) - 1` is zero. Interval arithmetic bounds it by the width
  `b - a` of the patch, so the two halves give `1/2`. The symbolic route gives `0`.

## Main results

Statements for every patch or every parameter. The nodal values are `u₀ = u false` at the
node `0` and `u₁ = u true` at the node `1`.

* `bubble_enclosed` (every patch `[a, b]` with `0 ≤ a` and `b ≤ 1`): the bubble takes values in
  `[a (1 - b), b (1 - a)]`.
* `hat_sum_enclosed` (every patch): `x + (1 - x)` takes values in `[a + (1 - b), b + (1 - a)]`.
* `neg_bubble_le` (every patch with `0 ≤ a` and `b ≤ 1`): `-(x (1 - x)) ≤ -(a (1 - b))`.
* `interpolant_le` (every patch, all `u₀, u₁ ≥ 0`): `u₁ x + u₀ (1 - x) ≤ u₁ b + u₀ (1 - a)`.
* `interpolant_approx` (all `u₀`, `u₁`, on `[0, 1]`): `u₁ x + u₀ (1 - x)` is within
  `|u₁| / 2 + |u₀| / 2` of `u₁ / 2 + u₀ / 2`.
* `bubble_approx` (every patch with `0 ≤ a` and `b ≤ 1`): the bubble is within
  `max |a| |b| * (1/2) + |1/2| * 0` of `x / 2`.
* `unity_defect` (every patch): `|x + (1 - x) - 1| ≤ b - a`.
* `unity_defect_exact` (every set): `|x + (1 - x) - 1| ≤ 0`.
* `width_nonneg_or_empty` (all `a`, `b`): `0 ≤ b - a` or `[a, b]` is empty.

One example each:

* `bubble_enclosed_restrict`: the enclosure `[0, 1]` of the bubble on `[0, 1]`, read on the
  left half.
* `bubble_enclosed_left`: the bubble lies in `[0, 3/8]` on the left half, from its two
  quarters.
* `bubble_le_quarters`: the bubble is at most `3/8` on `[0, 1]`, from the four quarters.
* `neg_bubble_le_middle`: the bubble is at least `1/8` on `[1/4, 3/4]`, from two patches,
  stated as an upper bound of its negative.
* `logistic_enclosed`: `4 x (1 - x)` lies in `[0, 2]` on the left half.
* `interpolant_enclosed`: `3 x - 2 (1 - x)` lies in `[-2, 3]` on `[0, 1]`.
* `interpolant_le_halves`: `3 x + 2 (1 - x) ≤ 4` on `[0, 1]`, from the two halves.
* `hat_sum_enclosed_halves`: `x + (1 - x)` lies in `[1/2, 3/2]` on `[0, 1]`, from the two halves.
* `hats_approx`: `x` is within `1/2 + 1/2` of `1 - x` on `[0, 1]`.
* `bubble_band`: on the left half the bubble lies in `[x / 2 - 1/4, x / 2 + 1/4]`.
* `bubble_approx_halves`: the bubble is within `1/2` of `x / 2` on `[0, 1]`, from the two
  halves.
* `sq_approx`: `x ^ 2` is within `1` of `(1 - x) / 2` on `[0, 1]`.
* `sin_bubble_approx`: `sin (x (1 - x))` is within `1/2` of `sin (x / 2)` on `[0, 1]`, from the
  two halves.
* `bubble_eqOn_point`: the bubble equals `x / 2` on the patch `[0, 0]`.
* `bubble_residual`: `|x (1 - x) - x / 2| ≤ 1/2` on the right half.
* `unity_defect_halves`, `unity_defect_uneven`: on `[0, 1]`, `|x + (1 - x) - 1|` is at most
  `1/2` from the two halves, and at most `3/4` from the patches `[0, 1/4]` and `[1/4, 1]`.

## Relations

The rules of `CAS.Certificate` and `CAS.Domain` that each declaration calls:

* `hat`: `EnclosureCert.sub`.
* `bubble_enclosed`: `enclosedOn_mul_nonneg`.
* `bubble_enclosed_restrict`: `EnclosureCert.sound_restrict`.
* `bubble_enclosed_left`: `EnclosureCert.union`, `EnclosureCert.sound_restrict`.
* `logistic_enclosed`: `EnclosureCert.scaleNonneg`.
* `interpolant_enclosed`: `enclosedOn_scale_nonpos`.
* `hat_sum_enclosed`: `EnclosureCert.sum`.
* `hat_sum_enclosed_halves`: `enclosedOn_union`.
* `neg_bubble_le`: `EnclosureCert.neg`, `BoundCert.ofEnclosure`.
* `neg_bubble_le_middle`: `boundOn_union`.
* `interpolant_le`: `BoundCert.ofEnclosure`, `BoundCert.scaleNonneg`, `BoundCert.sum`.
* `interpolant_le_halves`: `BoundCert.union`, `BoundCert.sound_restrict`.
* `hats_approx`: `ApproxCert.symm`, `ApproxCert.trans`.
* `interpolant_approx`: `ApproxCert.weightedSum`.
* `bubble_approx`: `ApproxCert.refl`, `ApproxCert.mulRealOfBoundCerts`, `BoundCert.const`.
* `bubble_band`: `ApproxCert.mem_Icc`.
* `bubble_approx_halves`: `ApproxAtlasCert.ofBinaryCover`, `ApproxAtlasCert.toApproxCert`.
* `sq_approx`: `ApproxCert.sub`.
* `sin_bubble_approx`: `ApproxCert.mapLipschitz`, `ApproxCert.union`,
  `ApproxCert.sound_restrict`.
* `bubble_eqOn_point`: `ApproxCert.eqOn_of_eps_eq_zero`.
* `bubble_residual`: `difference_residualBound_of_approxOn`.
* `unity_defect`: `EnclosureCert.sub`, `EnclosureCert.residualBound`.
* `unity_defect_halves`: `residualBound_union`.
* `unity_defect_uneven`: `ResidualCert.union`, `ResidualCert.sound_restrict`.
* `unity_defect_exact`: `ResidualCert.zero`.
* `width_nonneg_or_empty`: `ResidualCert.eps_nonneg_or_eq_empty`.
* `split`: `PatchCover.union`, `PatchCover.restrict`.
* `quarters`: `PatchCover.bind`.
* `bubble_le_quarters`: `PatchCover.lift`.

The atlas of `bubble_approx_halves` and `ApproxCert.union` in `sin_bubble_approx` glue in the
same way: the two certificates must have the same functions, and the larger budget is kept.
Other declarations of the library only connect the steps: the constructors `ofEnclosedOn`,
`ofBoundOn`, `ofApproxOn`, `ofResidualBound`, `ofRealEnclosureAround` and `absOfEnclosure`, and
lemmas such as `enclosedOn_mono`, `boundOn_mono` and `approxOn_mono_error`.

## Scope

Each of the 39 rules has an instance with real values on an interval of the real line.
`ApproxCert.weightedSum` and `ApproxCert.mapLipschitz` also take values in other normed spaces.
That case has no example here. There is no rule of `EnclosureCert` for interval multiplication
or for scaling by a negative number, so `bubble_enclosed` and `interpolant_enclosed` call the
relations `enclosedOn_mul_nonneg` and `enclosedOn_scale_nonpos`.
-/

@[expose] public section

noncomputable section

namespace CAS.Examples.CertificateAlgebra

open CAS.Certificate CAS.Domain

/-! ## Enclosures -/

/-- The identity on a patch `[a, b]` takes values in `[a, b]`. This is the only enclosure of
this module that is proved directly. All others come from rules. Every patch. -/
def idCert (a b : ℝ) : EnclosureCert ℝ (Set.Icc a b) :=
  .ofEnclosedOn (fun x ↦ x) a b fun _ hx ↦ hx

/-- The two hat functions on a patch `[a, b]`, with their ranges. The index is the node: `true`
is the node `1` and `false` is the node `0`. So `hat a b true` is `x` with the range `[a, b]`.
And `hat a b false` is `1 - x` with the range `[1 - b, 1 - a]`, by interval subtraction
(`EnclosureCert.sub`). Every patch. -/
def hat (a b : ℝ) : Bool → EnclosureCert ℝ (Set.Icc a b)
  | true => idCert a b
  | false => (EnclosureCert.const 1 _).sub (idCert a b)

/-- **Interval multiplication.** On a patch `[a, b]` inside `[0, 1]` both hats are nonnegative.
So `enclosedOn_mul_nonneg` multiplies their endpoints: the bubble `x * (1 - x)` takes values in
`[a * (1 - b), b * (1 - a)]`. A family: every patch with `0 ≤ a` and `b ≤ 1`. -/
theorem bubble_enclosed {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    EnclosedOn (fun x : ℝ ↦ x * (1 - x)) (Set.Icc a b) (a * (1 - b)) (b * (1 - a)) :=
  enclosedOn_mul_nonneg (hat a b true).sound (hat a b false).sound ha (sub_nonneg.2 hb)

/-- The enclosure `bubble_enclosed` as a certificate, for the rules that take certificates.
Every patch with `0 ≤ a` and `b ≤ 1`. -/
def bubbleCert (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) : EnclosureCert ℝ (Set.Icc a b) :=
  .ofEnclosedOn _ _ _ (bubble_enclosed ha hb)

/-- **Restriction keeps the endpoints.** On `[0, 1]` the certificate of the bubble has the
endpoints `0 * (1 - 1) = 0` and `1 * (1 - 0) = 1`. `EnclosureCert.sound_restrict` reads it on
the left half, where it still says `[0, 1]`. The certificate computed on the left half says
`[0, 1/2]`, and two quarters do better (`bubble_enclosed_left`). One example. -/
theorem bubble_enclosed_restrict :
    EnclosedOn (fun x : ℝ ↦ x * (1 - x)) (Set.Icc 0 (1 / 2)) 0 1 :=
  enclosedOn_mono
    ((bubbleCert 0 1 le_rfl le_rfl).sound_restrict _ (Set.Icc_subset_Icc le_rfl (by norm_num)))
    (by norm_num [bubbleCert, EnclosureCert.ofEnclosedOn])
    (by norm_num [bubbleCert, EnclosureCert.ofEnclosedOn])

/-- **Gluing two quarters.** The certificate of the bubble has the endpoints
`0 * (1 - 1/4) = 0` and `1/4 * (1 - 0) = 1/4` on `[0, 1/4]`, and `1/4 * (1 - 1/2) = 1/8` and
`1/2 * (1 - 1/4) = 3/8` on `[1/4, 1/2]`. `EnclosureCert.union` takes the smaller lower
endpoint, `min 0 (1/8)`, and the larger upper endpoint, `max (1/4) (3/8)`.
`EnclosureCert.sound_restrict` reads the result on the left half: the bubble lies in
`[0, 3/8]` there. One patch gives `[0, 1/2]`. One example. -/
theorem bubble_enclosed_left :
    EnclosedOn (fun x : ℝ ↦ x * (1 - x)) (Set.Icc 0 (1 / 2)) 0 (3 / 8) :=
  enclosedOn_mono
    -- The common function is written out. With `rfl`, Lean compares the two certificates first.
    (((bubbleCert 0 (1 / 4) le_rfl (by norm_num)).union
      (bubbleCert (1 / 4) (1 / 2) (by norm_num) (by norm_num))
      (Eq.refl fun x : ℝ ↦ x * (1 - x))).sound_restrict _ Set.Icc_subset_Icc_union_Icc)
    (by norm_num [EnclosureCert.union, bubbleCert, EnclosureCert.ofEnclosedOn])
    (by norm_num [EnclosureCert.union, bubbleCert, EnclosureCert.ofEnclosedOn])

/-- **Scaling by a nonnegative number.** `EnclosureCert.scaleNonneg` multiplies both endpoints
by `4`. On the left half the logistic map `4 * (x * (1 - x))` lies in
`[4 * (0 * (1 - 1/2)), 4 * (1/2 * (1 - 0))]`, which is `[0, 2]`. One example. -/
theorem logistic_enclosed :
    EnclosedOn (fun x : ℝ ↦ 4 * (x * (1 - x))) (Set.Icc 0 (1 / 2)) 0 2 :=
  enclosedOn_mono
    ((bubbleCert 0 (1 / 2) le_rfl (by norm_num)).scaleNonneg 4 (by norm_num)).sound
    (by norm_num [EnclosureCert.scaleNonneg, bubbleCert, EnclosureCert.ofEnclosedOn])
    (by norm_num [EnclosureCert.scaleNonneg, bubbleCert, EnclosureCert.ofEnclosedOn])

/-- **Scaling by a negative number swaps the endpoints.** The function `3 * x + -2 * (1 - x)`
is the linear interpolant with the value `-2` at the node `0` and `3` at the node `1`. On
`[0, 1]` the term `3 * x` lies in `[3 * 0, 3 * 1]`. By `enclosedOn_scale_nonpos` the term
`-2 * (1 - x)` lies in `[-2 * (1 - 0), -2 * (1 - 1)]`. The sum lies in `[-2, 3]`, the interval
between the two nodal values. One example. -/
theorem interpolant_enclosed :
    EnclosedOn (fun x : ℝ ↦ 3 * x + -2 * (1 - x)) (Set.Icc 0 1) (-2) 3 :=
  enclosedOn_mono
    (enclosedOn_add (enclosedOn_scale_nonneg (by norm_num) (hat 0 1 true).sound)
      (enclosedOn_scale_nonpos (by norm_num) (hat 0 1 false).sound))
    (by norm_num [hat, idCert, EnclosureCert.sub, EnclosureCert.const,
      EnclosureCert.ofEnclosedOn])
    (by norm_num [hat, idCert, EnclosureCert.sub, EnclosureCert.const,
      EnclosureCert.ofEnclosedOn])

/-- **A finite sum.** `EnclosureCert.sum` adds the endpoints of the two hats. On a patch
`[a, b]` the sum `x + (1 - x)` takes values in `[a + (1 - b), b + (1 - a)]`. The sum is the
constant `1`, but the enclosure has the width `2 * (b - a)`: interval arithmetic does not see
that the two terms cancel. A family: every patch. -/
theorem hat_sum_enclosed (a b : ℝ) :
    EnclosedOn (fun x : ℝ ↦ x + (1 - x)) (Set.Icc a b) (a + (1 - b)) (b + (1 - a)) := by
  simpa [Fintype.sum_bool, EnclosureCert.sum, hat, idCert, EnclosureCert.sub,
    EnclosureCert.const, EnclosureCert.ofEnclosedOn] using
    (EnclosureCert.sum Finset.univ (hat a b)).sound

/-- **Gluing enclosures with equal endpoints.** By `hat_sum_enclosed` the sum `x + (1 - x)`
lies in `[0 + (1 - 1/2), 1/2 + (1 - 0)]` on the left half and in
`[1/2 + (1 - 1), 1 + (1 - 1/2)]` on the right half. Both intervals are `[1/2, 3/2]`. So the
relation `enclosedOn_union` glues them: `x + (1 - x)` lies in `[1/2, 3/2]` on `[0, 1]`. One
patch gives `[0, 2]`. One example. -/
theorem hat_sum_enclosed_halves :
    EnclosedOn (fun x : ℝ ↦ x + (1 - x)) (Set.Icc 0 1) (1 / 2) (3 / 2) :=
  enclosedOn_mono_domain
    (enclosedOn_union
      (enclosedOn_mono (hat_sum_enclosed 0 (1 / 2)) (by norm_num) (by norm_num))
      (enclosedOn_mono (hat_sum_enclosed (1 / 2) 1) (by norm_num) (by norm_num)))
    Set.Icc_subset_Icc_union_Icc

/-! ## Upper bounds -/

/-- **A lower bound as an upper bound of the negative.** A `BoundCert` holds an upper bound
only. `EnclosureCert.neg` turns the enclosure of the bubble on a patch `[a, b]` into the
enclosure `[-(b * (1 - a)), -(a * (1 - b))]` of its negative, and `BoundCert.ofEnclosure`
keeps the upper endpoint: `-(x * (1 - x)) ≤ -(a * (1 - b))`. So the bubble is at least
`a * (1 - b)` on the patch. A family: every patch with `0 ≤ a` and `b ≤ 1`. -/
theorem neg_bubble_le {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    BoundOn (fun x : ℝ ↦ -(x * (1 - x))) (Set.Icc a b) (-(a * (1 - b))) :=
  (BoundCert.ofEnclosure (bubbleCert a b ha hb).neg).sound

/-- **Gluing bounds with one constant.** The bound of `neg_bubble_le` is `-(1/4 * (1 - 1/2))`
on `[1/4, 1/2]` and `-(1/2 * (1 - 3/4))` on `[1/2, 3/4]`. Both are `-(1/8)`. So the relation
`boundOn_union` glues them: `-(x * (1 - x)) ≤ -(1/8)` on `[1/4, 3/4]`, that is, the bubble is
at least `1/8` there. One patch gives `1/4 * (1 - 3/4) = 1/16`. One example. -/
theorem neg_bubble_le_middle :
    BoundOn (fun x : ℝ ↦ -(x * (1 - x))) (Set.Icc (1 / 4) (3 / 4)) (-(1 / 8)) :=
  boundOn_mono_domain
    (boundOn_union
      (boundOn_mono (neg_bubble_le (a := 1 / 4) (b := 1 / 2) (by norm_num) (by norm_num))
        (by norm_num))
      (boundOn_mono (neg_bubble_le (a := 1 / 2) (b := 3 / 4) (by norm_num) (by norm_num))
        (by norm_num)))
    Set.Icc_subset_Icc_union_Icc

/-- **A sum of scaled bounds.** Let `u false` and `u true` be nonnegative values at the nodes
`0` and `1`. `BoundCert.ofEnclosure` bounds each hat by its upper endpoint.
`BoundCert.scaleNonneg` multiplies the bound by the nodal value, and `BoundCert.sum` adds the
two. On a patch `[a, b]` the linear interpolant `u true * x + u false * (1 - x)` is at most
`u true * b + u false * (1 - a)`. A family: every patch and all nonnegative nodal values. -/
theorem interpolant_le (u : Bool → ℝ) (hu : ∀ i, 0 ≤ u i) (a b : ℝ) :
    BoundOn (fun x : ℝ ↦ u true * x + u false * (1 - x)) (Set.Icc a b)
      (u true * b + u false * (1 - a)) := by
  simpa [Fintype.sum_bool, BoundCert.sum, BoundCert.scaleNonneg, BoundCert.ofEnclosure, hat,
    idCert, EnclosureCert.sub, EnclosureCert.const, EnclosureCert.ofEnclosedOn] using
    (BoundCert.sum Finset.univ fun i ↦
      (BoundCert.ofEnclosure (hat a b i)).scaleNonneg (u i) (hu i)).sound

/-- **Gluing bound certificates.** For the nodal values `2` and `3`, `interpolant_le` gives the
bound `3 * (1/2) + 2 * (1 - 0) = 7/2` on the left half and `3 * 1 + 2 * (1 - 1/2) = 4` on the
right half. `BoundCert.union` keeps the larger one, `max (7/2) 4`, and
`BoundCert.sound_restrict` reads the result on `[0, 1]`: `3 * x + 2 * (1 - x) ≤ 4`. One patch
gives `3 * 1 + 2 * (1 - 0) = 5`. One example. -/
theorem interpolant_le_halves :
    BoundOn (fun x : ℝ ↦ 3 * x + 2 * (1 - x)) (Set.Icc 0 1) 4 := by
  have hu : ∀ i, (0 : ℝ) ≤ bif i then 3 else 2 := fun i ↦ by cases i <;> norm_num
  exact boundOn_mono
    (((BoundCert.ofBoundOn _ _ (interpolant_le _ hu 0 (1 / 2))).union
      (BoundCert.ofBoundOn _ _ (interpolant_le _ hu (1 / 2) 1))
      (Eq.refl fun x : ℝ ↦ 3 * x + 2 * (1 - x))).sound_restrict _ Set.Icc_subset_Icc_union_Icc)
    (by norm_num [BoundCert.union, BoundCert.ofBoundOn])

/-! ## Approximations -/

/-- Each hat is within `1/2` of the constant `1/2` on a patch `[a, b]` inside `[0, 1]`, because
its range lies in `[1/2 - 1/2, 1/2 + 1/2]` (`ApproxCert.ofRealEnclosureAround`). Every patch
with `0 ≤ a` and `b ≤ 1`. -/
def hatApprox (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) : Bool → ApproxCert ℝ ℝ (Set.Icc a b)
  | true => .ofRealEnclosureAround (hat a b true) (1 / 2) (1 / 2)
      ((sub_self _).trans_le ha) (hb.trans_eq (add_halves 1).symm)
  | false => .ofRealEnclosureAround (hat a b false) (1 / 2) (1 / 2)
      ((sub_self _).trans_le (sub_nonneg.2 hb)) ((sub_le_self 1 ha).trans_eq (add_halves 1).symm)

/-- **Symmetry and transitivity.** On `[0, 1]` the hat `x` is within `1/2` of the constant
`1/2`. By `ApproxCert.symm` the constant `1/2` is within `1/2` of the hat `1 - x`.
`ApproxCert.trans` adds the two budgets: `x` is within `1/2 + 1/2` of `1 - x`. One example. -/
theorem hats_approx :
    ApproxOn (fun x : ℝ ↦ x) (fun x ↦ 1 - x) (Set.Icc 0 1) (1 / 2 + 1 / 2) :=
  ((hatApprox 0 1 le_rfl le_rfl true).trans (hatApprox 0 1 le_rfl le_rfl false).symm rfl).sound

/-- **A weighted sum.** `ApproxCert.weightedSum` combines the certificates of the two hats,
with the nodal values `u false` and `u true` as weights. The weights may have any sign, and
each enters the budget with its absolute value. On `[0, 1]` the linear interpolant
`u true * x + u false * (1 - x)` is within `|u true| * (1/2) + |u false| * (1/2)` of the
constant `u true * (1/2) + u false * (1/2)`. A family: all nodal values. -/
theorem interpolant_approx (u : Bool → ℝ) :
    ApproxOn (fun x : ℝ ↦ u true * x + u false * (1 - x))
      (fun _ ↦ u true * (1 / 2) + u false * (1 / 2)) (Set.Icc 0 1)
      (|u true| * (1 / 2) + |u false| * (1 / 2)) := by
  simpa [Fintype.sum_bool, ApproxCert.weightedSum, hatApprox, ApproxCert.ofRealEnclosureAround,
    hat, idCert, EnclosureCert.sub, EnclosureCert.const, EnclosureCert.ofEnclosedOn] using
    (ApproxCert.weightedSum u (hatApprox 0 1 le_rfl le_rfl)).sound

/-- **The product rule.** On a patch `[a, b]` inside `[0, 1]` take the factor `x` as it is
(`ApproxCert.refl`, budget `0`) and the factor `1 - x` frozen at `1/2` (budget `1/2`).
`ApproxCert.mulRealOfBoundCerts` needs a bound `A` of `|x|` and a bound `B` of the frozen
value. Here `A` is `max |a| |b|`, from the range of `x`, and `B` is `|1/2|`, from
`BoundCert.const`. The budget of the product is `A * (1/2) + B * 0`: the bubble `x * (1 - x)`
is within `max |a| |b| * (1/2) + |1/2| * 0` of the model `x * (1/2)`. A family: every patch
with `0 ≤ a` and `b ≤ 1`. -/
theorem bubble_approx {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    ApproxOn (fun x : ℝ ↦ x * (1 - x)) (fun x ↦ x * (1 / 2)) (Set.Icc a b)
      (max |a| |b| * (1 / 2) + |1 / 2| * 0) :=
  ((ApproxCert.refl (fun x ↦ x) _).mulRealOfBoundCerts (hatApprox a b ha hb false)
    (BoundCert.absOfEnclosure (hat a b true)) (BoundCert.const |1 / 2| _) rfl rfl).sound

/-- The approximation `bubble_approx` as a certificate, for the rules that take certificates.
Every patch with `0 ≤ a` and `b ≤ 1`. -/
def bubbleApprox (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) : ApproxCert ℝ ℝ (Set.Icc a b) :=
  .ofApproxOn _ _ _ (bubble_approx ha hb)

/-- **A band around the model.** On the left half the budget of `bubbleApprox` is
`max |0| |1/2| * (1/2) + |1/2| * 0`, which is `1/4`. `ApproxCert.mem_Icc` turns the certificate
into an interval at each point: for `x` in `[0, 1/2]` the bubble lies in
`[x * (1/2) - 1/4, x * (1/2) + 1/4]`. One example. -/
theorem bubble_band {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    x * (1 - x) ∈ Set.Icc (x * (1 / 2) - 1 / 4) (x * (1 / 2) + 1 / 4) :=
  Set.Icc_subset_Icc (by norm_num [bubbleApprox, ApproxCert.ofApproxOn])
    (by norm_num [bubbleApprox, ApproxCert.ofApproxOn])
    ((bubbleApprox 0 (1 / 2) le_rfl (by norm_num)).mem_Icc hx)

/-- **Two halves glued by an atlas.** The budget of `bubbleApprox` is `1/4` on the left half.
On the right half it is `max |1/2| |1| * (1/2) + |1/2| * 0`, which is `1/2`.
`ApproxAtlasCert.ofBinaryCover` puts the two certificates on the cover of `[0, 1]` by its
halves, with the global budget `max (1/4) (1/2)`. `ApproxAtlasCert.toApproxCert` forgets the
cover: on `[0, 1]` the bubble is within `1/2` of `x * (1/2)`. At `x = 1` the two functions
differ by `1/2`. One example. -/
theorem bubble_approx_halves :
    ApproxOn (fun x : ℝ ↦ x * (1 - x)) (fun x ↦ x * (1 / 2)) (Set.Icc 0 1) (1 / 2) :=
  approxOn_mono_error
    (ApproxAtlasCert.ofBinaryCover Set.Icc_subset_Icc_union_Icc
      (bubbleApprox 0 (1 / 2) le_rfl (by norm_num)) (bubbleApprox (1 / 2) 1 (by norm_num) le_rfl)
      (Eq.refl fun x : ℝ ↦ x * (1 - x)) (Eq.refl fun x : ℝ ↦ x * (1 / 2))).toApproxCert.sound
    (by norm_num [ApproxAtlasCert.toApproxCert, ApproxAtlasCert.ofBinaryCover,
      FunctionBudgetAtlasCert.ofBinaryCover, bubbleApprox, ApproxCert.ofApproxOn])

/-- **Subtraction.** The square is the hat `x` minus the bubble: `x ^ 2 = x - x * (1 - x)`. On
`[0, 1]` the hat is within `1/2` of the constant `1/2`, and the bubble is within
`max |0| |1| * (1/2) + |1/2| * 0 = 1/2` of `x * (1/2)`. `ApproxCert.sub` subtracts the two
certificates and adds their budgets: `x ^ 2` is within `1/2 + 1/2` of `1/2 - x * (1/2)`, that
is, within `1` of `(1 - x) / 2`. At `x = 1` the two differ by `1`. One example. -/
theorem sq_approx : ApproxOn (fun x : ℝ ↦ x ^ 2) (fun x ↦ (1 - x) / 2) (Set.Icc 0 1) 1 := by
  have h : ApproxOn (fun x : ℝ ↦ x - x * (1 - x)) (fun x ↦ 1 / 2 - x * (1 / 2)) (Set.Icc 0 1) _ :=
    ((hatApprox 0 1 le_rfl le_rfl true).sub (bubbleApprox 0 1 le_rfl le_rfl)).sound
  exact approxOn_mono_error (approxOn_congr h subset_rfl (fun x _ ↦ by ring) fun x _ ↦ by ring)
    (by norm_num [ApproxCert.sub, hatApprox, ApproxCert.ofRealEnclosureAround, bubbleApprox,
      ApproxCert.ofApproxOn])

/-- **A Lipschitz map, then gluing.** The sine has the Lipschitz constant `1`.
`ApproxCert.mapLipschitz` carries the certificate of the bubble through the sine and
multiplies its budget by this constant: `1 * (1/4)` on the left half and `1 * (1/2)` on the
right half. `ApproxCert.union` keeps the larger budget, and `ApproxCert.sound_restrict` reads
the result on `[0, 1]`: `sin (x * (1 - x))` is within `1/2` of `sin (x * (1/2))`. One
example. -/
theorem sin_bubble_approx :
    ApproxOn (fun x : ℝ ↦ Real.sin (x * (1 - x))) (fun x ↦ Real.sin (x * (1 / 2)))
      (Set.Icc 0 1) (1 / 2) := by
  have hsin : ∀ x y : ℝ, ‖Real.sin x - Real.sin y‖ ≤ 1 * ‖x - y‖ := fun x y ↦
    (Real.abs_sin_sub_sin_le x y).trans_eq (one_mul _).symm
  exact approxOn_mono_error
    ((((bubbleApprox 0 (1 / 2) le_rfl (by norm_num)).mapLipschitz Real.sin 1 zero_le_one hsin).union
      ((bubbleApprox (1 / 2) 1 (by norm_num) le_rfl).mapLipschitz Real.sin 1 zero_le_one hsin)
      (Eq.refl fun x : ℝ ↦ Real.sin (x * (1 - x)))
      (Eq.refl fun x : ℝ ↦ Real.sin (x * (1 / 2)))).sound_restrict _
        Set.Icc_subset_Icc_union_Icc)
    (by norm_num [ApproxCert.union, ApproxCert.mapLipschitz, bubbleApprox, ApproxCert.ofApproxOn])

/-- **A zero budget is an identity.** On the patch `[0, 0]` the bound of `|x|` is
`max |0| |0|`, so the budget of `bubbleApprox` is `0 * (1/2) + |1/2| * 0 = 0`.
`ApproxCert.eqOn_of_eps_eq_zero` turns the zero budget into an equality: the bubble equals its
model `x * (1/2)` on `[0, 0]`. One example. -/
theorem bubble_eqOn_point :
    Set.EqOn (fun x : ℝ ↦ x * (1 - x)) (fun x ↦ x * (1 / 2)) (Set.Icc 0 0) :=
  (bubbleApprox 0 0 le_rfl zero_le_one).eqOn_of_eps_eq_zero
    (by norm_num [bubbleApprox, ApproxCert.ofApproxOn])

/-! ## Residuals -/

/-- **An approximation as a residual bound.** `difference_residualBound_of_approxOn` reads the
approximation of the bubble by its model as a bound on their difference. On the right half the
budget is `max |1/2| |1| * (1/2) + |1/2| * 0`, which is `1/2`:
`|x * (1 - x) - x * (1/2)| ≤ 1/2`. At `x = 1` the difference is `-1/2`. One example. -/
theorem bubble_residual :
    ResidualBound (fun x : ℝ ↦ x * (1 - x) - x * (1 / 2)) (Set.Icc (1 / 2) 1) (1 / 2) :=
  difference_residualBound_of_approxOn
    (approxOn_mono_error (bubble_approx (a := 1 / 2) (b := 1) (by norm_num) le_rfl)
      (by norm_num))

/-- **From an enclosure to a residual bound.** Subtracting the constant `1` from the enclosure
`hat_sum_enclosed` puts the defect `x + (1 - x) - 1` in `[a + (1 - b) - 1, b + (1 - a) - 1]`,
which is `[-(b - a), b - a]`. `EnclosureCert.residualBound` reads this as a residual bound
whose budget is the width `b - a` of the patch. The defect is zero, but interval arithmetic
does not see the cancellation. A family: every patch. -/
theorem unity_defect (a b : ℝ) :
    ResidualBound (fun x : ℝ ↦ x + (1 - x) - 1) (Set.Icc a b) (b - a) :=
  ((EnclosureCert.ofEnclosedOn _ _ _ (hat_sum_enclosed a b)).sub
    (EnclosureCert.const 1 _)).residualBound
      (le_of_eq (by ring : -(b - a) = a + (1 - b) - 1))
      (le_of_eq (by ring : b + (1 - a) - 1 = b - a))

/-- The bound `unity_defect` as a residual certificate. Its budget is `b - a`. Every patch. -/
def unityCert (a b : ℝ) : ResidualCert ℝ ℝ (Set.Icc a b) :=
  .ofResidualBound _ _ (unity_defect a b)

/-- **Gluing residual bounds with one budget.** On the two halves the budgets of
`unity_defect` are `1/2 - 0` and `1 - 1/2`. Both are `1/2`. So the relation
`residualBound_union` glues them: `|x + (1 - x) - 1| ≤ 1/2` on `[0, 1]`. One patch gives
`1 - 0`. One example. -/
theorem unity_defect_halves :
    ResidualBound (fun x : ℝ ↦ x + (1 - x) - 1) (Set.Icc 0 1) (1 / 2) :=
  residualBound_mono_domain
    (residualBound_union
      (approxOn_mono_error (unity_defect 0 (1 / 2)) (by norm_num))
      (approxOn_mono_error (unity_defect (1 / 2) 1) (by norm_num)))
    Set.Icc_subset_Icc_union_Icc

/-- **Gluing residual certificates.** On the patches `[0, 1/4]` and `[1/4, 1]` the budgets of
`unityCert` are `1/4 - 0` and `1 - 1/4`. `ResidualCert.union` keeps the larger one,
`max (1/4) (3/4)`, and `ResidualCert.sound_restrict` reads the result on `[0, 1]`:
`|x + (1 - x) - 1| ≤ 3/4`. The wider patch decides. The two halves give `1/2`
(`unity_defect_halves`). One example. -/
theorem unity_defect_uneven :
    ResidualBound (fun x : ℝ ↦ x + (1 - x) - 1) (Set.Icc 0 1) (3 / 4) :=
  approxOn_mono_error
    (((unityCert 0 (1 / 4)).union (unityCert (1 / 4) 1)
      (Eq.refl fun x : ℝ ↦ x + (1 - x) - 1)).sound_restrict _ Set.Icc_subset_Icc_union_Icc)
    (by norm_num [ResidualCert.union, unityCert, ResidualCert.ofResidualBound])

/-- **The symbolic route.** The defect `x + (1 - x) - 1` is the zero function, by `ring`. So
the zero certificate `ResidualCert.zero`, with the budget `0`, can be moved to this formula.
The defect has the residual bound `0` on every set, where interval arithmetic gives the width
of the patch. All sets. -/
theorem unity_defect_exact (s : Set ℝ) : ResidualBound (fun x : ℝ ↦ x + (1 - x) - 1) s 0 :=
  ((ResidualCert.zero s).replaceResidual (fun x ↦ x + (1 - x) - 1) fun x _ ↦
    (by ring : x + (1 - x) - 1 = (0 : ℝ))).sound

/-- **A budget is nonnegative unless the patch is empty.** The budget of `unityCert a b` is
`b - a`, for all real `a` and `b`. `ResidualCert.eps_nonneg_or_eq_empty` says about this
certificate that `0 ≤ b - a` or the interval `[a, b]` is empty. Both cases occur: on `[0, 1]`
the budget is `1`, and on the empty interval `[1, 0]` it is `-1`. All `a` and `b`. -/
theorem width_nonneg_or_empty (a b : ℝ) : 0 ≤ b - a ∨ Set.Icc a b = ∅ :=
  (unityCert a b).eps_nonneg_or_eq_empty

/-! ## Covers -/

/-- The cover of `[a, b]` by the two patches `[a, m]` and `[m, b]`. `PatchCover.union` covers
the union of the two patches, and `PatchCover.restrict` keeps this cover for `[a, b]`, which
the union contains. The index `true` is `[a, m]` and `false` is `[m, b]`. All `a`, `m` and
`b`. -/
def split (a m b : ℝ) : PatchCover ℝ Bool (Set.Icc a b) :=
  (PatchCover.union (Set.Icc a m) (Set.Icc m b)).restrict Set.Icc_subset_Icc_union_Icc

/-- The cover of `[0, 1]` by its four quarters. `PatchCover.bind` cuts each half of
`split 0 (1/2) 1` again. The index `⟨i, j⟩` names the half `i` and the quarter `j` inside it:
`⟨true, true⟩` is `[0, 1/4]` and `⟨false, false⟩` is `[3/4, 1]`. One cover. -/
def quarters : PatchCover ℝ (Σ _ : Bool, Bool) (Set.Icc 0 1) :=
  (split 0 (1 / 2) 1).bind fun
    | true => split 0 (1 / 4) (1 / 2)
    | false => split (1 / 2) (3 / 4) 1

/-- **Four quarters.** On the quarters the upper endpoints `b * (1 - a)` of `bubble_enclosed`
are `1/4`, `3/8`, `3/8` and `1/4`. `PatchCover.lift` carries the four local bounds to the
covered interval: `x * (1 - x) ≤ 3/8` on `[0, 1]`. One patch gives `1` and two halves give
`1/2`. One example. -/
theorem bubble_le_quarters : BoundOn (fun x : ℝ ↦ x * (1 - x)) (Set.Icc 0 1) (3 / 8) :=
  quarters.lift (P := fun x ↦ x * (1 - x) ≤ 3 / 8) fun
    | ⟨true, true⟩ => boundOn_mono
        (enclosedOn_upper (bubble_enclosed (a := 0) (b := 1 / 4) le_rfl (by norm_num)))
        (by norm_num)
    | ⟨true, false⟩ => boundOn_mono
        (enclosedOn_upper (bubble_enclosed (a := 1 / 4) (b := 1 / 2) (by norm_num) (by norm_num)))
        (by norm_num)
    | ⟨false, true⟩ => boundOn_mono
        (enclosedOn_upper (bubble_enclosed (a := 1 / 2) (b := 3 / 4) (by norm_num) (by norm_num)))
        (by norm_num)
    | ⟨false, false⟩ => boundOn_mono
        (enclosedOn_upper (bubble_enclosed (a := 3 / 4) (b := 1) (by norm_num) le_rfl))
        (by norm_num)

/-! ## Axioms -/

set_option linter.hashCommand false

/-- info: 'CAS.Examples.CertificateAlgebra.bubble_le_quarters' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bubble_le_quarters

/-- info: 'CAS.Examples.CertificateAlgebra.bubble_approx_halves' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bubble_approx_halves

/-- info: 'CAS.Examples.CertificateAlgebra.unity_defect_halves' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unity_defect_halves

end CAS.Examples.CertificateAlgebra

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Cert.Reduce
public meta import CAS.Cert.Reduce
public import CAS.Cert.Leaves
public meta import CAS.Cert.Leaves
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A structure of conditions: which fields a computation decides

## Motivation

The hypothesis of a computer-assisted theorem, such as `CellLayerSystem.CellSystemCondition` of
BlowupZoo's Navier-Stokes statement, is a structure of conditions on data: relations between
numbers, bounds at every point of an interval or a box, bounds on polynomials, and facts that
no finite computation decides, such as an integral or a regularity statement. For given data,
what does the framework close, what does it leave, and how is a checker for such a structure
assembled when the data are an input?

## The idea

`Profile` is an invented structure of twelve conditions on a datum of two numbers, four
coefficients and a function. `#cert_leaves` lists its conditions with a class for each.
`cert_reduce` applies the constructors, closes nine conditions by computation in the kernel and
returns the three others as the hypotheses of a theorem; here they are then proved by hand, so
the structure holds for the invented datum.

The last section assembles a checker for a structure `Sound` whose data are an input, an
integer for every entry: one `Check` for every field, joined by `Check.and`, with `Check.or`
for a disjunction, `Check.allFin` for a field over `Fin 4`, `Check.pairs` for a field over
pairs of entries and `Check.onCover` for a field on an interval that is checked on four cells.

## Main results

* `profile_of_open` (one example: the invented datum): `Profile datum` from its three fields
  that are not computations. The other nine are closed by `cert_decide`: four relations between
  numbers with a square root, `π`, an exponential and a sine, a bound and a `≠` over `Fin 4`, an
  equality, a cubic on `[0, 1]`, and a polynomial in two variables on the unit square.
* `profile` (the same example): `Profile datum`, with the three open fields proved by hand.
* `check`, `sound_of_run` (all integer data): a checker for `Sound`, and the theorem that a
  passing run proves `Sound` for the real numbers that the data stand for; `sound_example` runs
  it on one datum.

## Relations

`profile_of_open` is written by `cert_reduce` ([Reduce](../../Cert/Reduce.lean)); each closed
field is one application of `holds_closed` or `rel_of_ratTest`. `check` uses the combinators of
[Check](../../Cert/Check.lean) with `Cond.holds_of_run` ([Cond](../../Cert/Cond.lean)) at every
leaf, and `exists_cell` for the cover. The listing is that of
[Leaves](../../Cert/Leaves.lean). The NSCert checker of BlowupZoo runs its `nscert_reduce` on a
structure of the same shape.

## Scope

The data are invented. `CellLayerSystem.CellSystemCondition` has 3,007 leaves and data of seven
kinds; its fields about integrals and about the definitions of its own package need bridge
theorems that are not part of this library.
-/

set_option linter.hashCommand false

@[expose] public section

namespace CAS.Examples.Cert.Structure

open CAS.Cert CAS.Numerics CAS.Verified

/-! ### One datum: the fields that a computation decides -/

/-- A datum: two numbers, the four coefficients of a cubic, and a function. -/
structure Datum where
  /-- The first number. -/
  ν : ℝ
  /-- A second number. -/
  r : ℝ
  /-- The coefficients of a cubic. -/
  c : Fin 4 → ℝ
  /-- A function. -/
  f : ℝ → ℝ

/-- Conditions between the numbers of a datum. -/
structure Numbers (d : Datum) : Prop where
  /-- The first number is positive. -/
  ν_pos : 0 < d.ν
  /-- A bound with a square root and `π`. -/
  root : Real.sqrt d.r ≤ Real.pi / 2
  /-- A bound with an exponential. -/
  decay : Real.exp (-d.ν) + d.r / 4 < 1
  /-- A bound with a sine. -/
  angle : Real.sin d.ν ≤ 9 / 10
  /-- The coefficients are small. -/
  c_small : ∀ j, |d.c j| ≤ 4
  /-- No coefficient is zero. -/
  c_ne : ∀ j, d.c j ≠ 0
  /-- The coefficients add up to `3 / 8`. -/
  c_sum : d.c 0 + d.c 1 + d.c 2 + d.c 3 = 3 / 8

/-- All conditions on a datum: the conditions between its numbers, a bound for its cubic on
`[0, 1]`, a bound on the unit square, and three conditions on its function. -/
structure Profile (d : Datum) : Prop where
  /-- The conditions between the numbers. -/
  numbers : Numbers d
  /-- The cubic is at most `1 / 2` on `[0, 1]`. -/
  cubic_le : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
    d.c 0 + d.c 1 * x + d.c 2 * x ^ 2 + d.c 3 * x ^ 3 ≤ 1 / 2
  /-- A polynomial in two variables is positive on the unit square. -/
  square_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
    0 < d.ν + x * y - d.r * x ^ 2 * y
  /-- The function is at most the first number. -/
  f_le : ∀ x, d.f x ≤ d.ν
  /-- The function is continuous. -/
  f_cont : Continuous d.f
  /-- The integral of the function over `[0, 1]` is the second number. -/
  mass : ∫ x in (0 : ℝ)..1, d.f x = d.r

/-- The numerators of the coefficients at the scale `1 / 8`. -/
def numerators : List ℤ := [3, -10, 28, -18]

/-- The invented datum: `ν = 1 / 2`, `r = 1 / 4`, the cubic
`(3 - 10 x + 28 x ^ 2 - 18 x ^ 3) / 8`, and the function `1 / 2 - 3 x ^ 2 / 4`. -/
noncomputable def datum : Datum where
  ν := 1 / 2
  r := 1 / 4
  c := fun j ↦ ((numerators.getD j.val 0 : ℤ) : ℝ) / 8
  f := fun x ↦ 1 / 2 - 3 / 4 * x ^ 2

/-- **The structure from its open fields.** `Profile datum` holds if its three fields about the
function hold. The other nine conditions are closed by computation in the kernel. -/
cert_reduce profile_of_open (leaving := [f_le, f_cont, mass]) : Profile datum

/-- `Profile datum` holds: the three fields that are not computations are proved by hand. -/
theorem profile : Profile datum := by
  refine profile_of_open (fun x ↦ ?_) ?_ ?_
  · have := sq_nonneg x
    simp only [datum]
    linarith
  · unfold datum
    fun_prop
  · simp only [datum]
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (by apply Continuous.intervalIntegrable; fun_prop)]
    simp [integral_pow]
    norm_num

/-! ### A checker over data, assembled field by field -/

/-- Conditions on real data `v`, indexed by natural numbers: entry `0` is positive, the square
root of entry `1` is at most `π / 2`, entry `2` is negative or below one, the entries `2` to `5`
are small and close to each other, and the cubic with these coefficients is at most `1 / 2` on
`[0, 1]`. -/
structure Sound (v : ℕ → ℝ) : Prop where
  /-- Entry `0` is positive. -/
  pos : 0 < v 0
  /-- The square root of entry `1` is at most `π / 2`. -/
  root : Real.sqrt (v 1) ≤ Real.pi / 2
  /-- Entry `2` is negative or below one. -/
  sign : v 2 < 0 ∨ v 2 < 1
  /-- The entries `2` to `5` are at most `4` in absolute value. -/
  small : ∀ j : Fin 4, |v (2 + j.val)| ≤ 4
  /-- Any two of the entries `2` to `5` differ by at most `6`. -/
  spread : ∀ i, i < 4 → ∀ j, j < 4 → v (2 + i) - v (2 + j) ≤ 6
  /-- The cubic with the coefficients `2` to `5` is at most `1 / 2` on `[0, 1]`. -/
  cubic : ∀ x ∈ Set.Icc (0 : ℝ) 1, v 2 + x * (v 3 + x * (v 4 + x * v 5)) ≤ 1 / 2

/-- The real number of entry `i` of integer data `d`, at the scale `1 / 8`. -/
noncomputable def val (d : ℕ → ℤ) (i : ℕ) : ℝ := (d i : ℝ) / (8 : ℕ)

/-- The ball of entry `i` of integer data `d`, at 64 bits. -/
def rawBall (d : ℕ → ℤ) (i : ℕ) : GridBall :=
  GridBall.ofFrac 64 (decide (d i < 0)) (d i).natAbs 8

/-- The balls of integer data enclose their real numbers. -/
theorem rawBall_encloses (d : ℕ → ℤ) (i : ℕ) : (rawBall d i).EnclosesReal 64 (val d i) :=
  GridBall.enclosesReal_ofFrac 64 (d i) 8

/-- The condition that the cubic of the entries `2` to `5` is at most `1 / 2` on the cell
`[k / 4, (k + 1) / 4]`. -/
def cubicCond (k : ℕ) : Cond ℕ :=
  .onIcc (.rat k 4) (.rat (k + 1) 4) 6
    (.le (.add (Cond.dat 2) (.mul (Cond.cell 0) (.add (Cond.dat 3) (.mul (Cond.cell 0)
      (.add (Cond.dat 4) (.mul (Cond.cell 0) (Cond.dat 5))))))) (.rat 1 2))

/-- The four cells `[k / 4, (k + 1) / 4]` cover `[0, 1]`. -/
theorem cover (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ k : ℕ, k < 4 ∧ x ∈ Set.Icc ((k : ℝ) / 4) (((k + 1 : ℕ) : ℝ) / 4) := by
  obtain ⟨k, hk, h1, h2⟩ := exists_cell (t := fun k ↦ (k : ℝ) / 4) (n := 4) (by norm_num)
    (by simpa using hx.1) (by norm_num; exact hx.2)
  exact ⟨k, hk, h1, h2⟩

/-- **A checker for a structure, field by field.** For integer data `d`, a check of
`Sound (val d)`: one check for every field, joined by `Check.and`. Its test is a Boolean that
depends on `d` only. -/
def check (d : ℕ → ℤ) : Check (Sound (val d)) :=
  let leaf (c : Cond ℕ) : Check (c.holds (val d) fun _ ↦ 0) :=
    ⟨c.run 64 (rawBall d), Cond.holds_of_run (rawBall_encloses d) c _⟩
  (((((leaf (.lt (.nat 0) (Cond.dat 0))).and
      (leaf (.le (.sqrt (Cond.dat 1)) (.div .pi (.nat 2))))).and
      ((leaf (.lt (Cond.dat 2) (.nat 0))).or (leaf (.lt (Cond.dat 2) (.nat 1))))).and
      (Check.allFin fun j : Fin 4 ↦ leaf (.le (absE (Cond.dat (2 + j.val))) (.nat 4)))).and
      ((Check.pairs 4 4 fun i j ↦
        leaf (.le (.sub (Cond.dat (2 + i)) (Cond.dat (2 + j))) (.nat 6))).and
      (Check.onCover (S := fun x ↦ x ∈ Set.Icc (0 : ℝ) 1)
        (cell := fun k x ↦ x ∈ Set.Icc ((k : ℝ) / 4) (((k + 1 : ℕ) : ℝ) / 4))
        (C := fun x ↦ val d 2 + x * (val d 3 + x * (val d 4 + x * val d 5)) ≤ 1 / 2)
        4 cover fun k ↦ (leaf (cubicCond k)).mono fun h x hx ↦ by
          have := h x (by simpa [Cond.holds] using hx.1) (by simpa [Cond.holds] using hx.2)
          simpa [cubicCond, Cond.holds] using this))).mono fun h ↦
    { pos := by simpa [Cond.holds] using h.1.1.1.1
      root := by simpa [Cond.holds] using h.1.1.1.2
      sign := by simpa [Cond.holds] using h.1.1.2
      small := fun j ↦ by simpa [Cond.holds, eval_absE] using h.1.2 j
      spread := fun i hi j hj ↦ by simpa [Cond.holds] using h.2.1 i hi j hj
      cubic := h.2.2 }

/-- **A run proves the structure.** For all integer data `d`: if the test of `check d` passes,
then `Sound` holds for the real numbers that `d` stands for. -/
theorem sound_of_run (d : ℕ → ℤ) (h : (check d).run = true) : Sound (val d) :=
  (check d).sound h

/-- Integer data: `ν = 1 / 2`, `r = 1 / 4`, and the coefficients of `numerators`. -/
def raw : ℕ → ℤ := fun i ↦ ([4, 2] ++ numerators).getD i 0

/-- The checker accepts the data `raw`: `Sound` holds for them. -/
theorem sound_example : Sound (val raw) :=
  sound_of_run raw (by cert_eval [check, raw, numerators, rawBall, cubicCond])

end CAS.Examples.Cert.Structure

/-- info: leaves of CAS.Examples.Cert.Structure.Profile
structures entered: 2, their fields: 13, definitions unfolded: 0, leaves: 12, leaves under an existential quantifier: 0
classes: NUM 6, EQ 1, MAT 0, INF 0, PT 3, INT 1, REG 1, OTHER 0
LEAF	1	NUM	0	numbers.ν_pos	LT.lt		0 < d.ν
LEAF	2	NUM	0	numbers.root	LE.le		√d.r ≤ Real.pi / 2
LEAF	3	NUM	0	numbers.decay	LT.lt		Real.exp (-d.ν) + d.r / 4 < 1
LEAF	4	NUM	0	numbers.angle	LE.le		Real.sin d.ν ≤ 9 / 10
LEAF	5	NUM	0	numbers.c_small	LE.le	∀ j : Fin 4	|d.c j| ≤ 4
LEAF	6	NUM	0	numbers.c_ne	Ne	∀ j : Fin 4	d.c j ≠ 0
LEAF	7	EQ	0	numbers.c_sum	Eq		d.c 0 + d.c 1 + d.c 2 + d.c 3 = 3 / 8
LEAF	8	PT	0	cubic_le	LE.le	∀ x : ℝ ; 0 ≤ x ; x ≤ 1	d.c 0 + d.c 1 * x + d.c 2 * x ^ 2 + d.c 3 * x ^ 3 ≤ 1 / 2
LEAF	9	PT	0	square_pos	LT.lt	∀ x : ℝ ; x ∈ Set.Icc 0 1 ; ∀ y : ℝ ; y ∈ Set.Icc 0 1	0 < d.ν + x * y - d.r * x ^ 2 * y
LEAF	10	PT	0	f_le	LE.le	∀ x : ℝ	d.f x ≤ d.ν
LEAF	11	REG	0	f_cont	Continuous		Continuous d.f
LEAF	12	INT	0	mass	Eq		∫ (x : ℝ) in 0..1, d.f x = d.r
-/
#guard_msgs in
#cert_leaves CAS.Examples.Cert.Structure.Profile

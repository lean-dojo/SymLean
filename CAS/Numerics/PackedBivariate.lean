/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedSignedRows
public import CAS.Numerics.PackedLinearAlgebra
public import CAS.Numerics.PackedSpread
public import CAS.Numerics.MatrixPositivity
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact integrals of polynomial expressions in two variables, on packed rows

## Motivation

A certificate of an approximate solution of a differential equation has to bound the integral
of the square of its residual. When the solution is a polynomial on each cell of a mesh, the
residual is a polynomial too. Can the kernel compute the integral exactly, with a few
big-number products per cell, instead of enclosing the residual point by point? This is the
question behind the bound for the residual of the approximate profile in BlowupZoo's statement
of the unforced Navier-Stokes blowup.

## The idea

A polynomial in `(x, y)` of degree below `n` in `x` is stored as one integer: the coefficient
of `x ^ i y ^ j` sits in slot `i + S j` of a signed packed row, for a stride `S`. The product of
two such integers is the packed row of the product polynomial, as long as the degrees in `x`
add up to less than `S` (Kronecker substitution in two variables), sums are sums, and a
derivative moves every slot and multiplies it by its exponent. So a residual such as
`ν (u_xx + u_yy) - u u_x - f` is evaluated on the integers of `u` and `f` and gives the integer
of the residual polynomial, with no rounding. The integral over the unit square of
`x ^ i y ^ j` is `1 / ((i + 1) (j + 1))`. With a common multiple `D` of these denominators, `D`
times the integral of a polynomial is the sum of its coefficients times the integers
`D / ((i + 1) (j + 1))`, and this sum is one slot of the product of the packed polynomial with
the packed row of these integers in reverse order. The integral of the square of a residual
`R` is the integral of the expression `R * R`.

## Main results

* `bivEval_zConv` (all coefficient rows): the convolution of two rows is the product of the
  polynomials, when the degrees in `x` are below `n` and `n'` with `n + n' ≤ S + 1`.
* `hasDerivAt_bivEval_x`, `hasDerivAt_bivEval_y` (all rows, positive stride): the rows `dxCoef`,
  `dyCoef` are the partial derivatives.
* `integral_bivEval` (all rows): the integral over the unit square.
* `BivExpr.eval_eq`, `BivExpr.pack_eq` (all expressions built from variables, integer
  multiples, sums, products and partial derivatives that pass the test `BivExpr.ok`): the real
  value of an expression is the polynomial of its coefficient row, and the integer computed from
  the packed variables is the packed coefficient row.
* `zSlotComb_zPack`, `rowOfNat_eq`, `momentNum_eq` (all rows, under their fit conditions): the
  slot map behind the partial derivatives, the reading of a stored row under its guard, and the
  slot of the product with the row of the moments, which is `D` times the integral.
* `BivExpr.integral_eq` (all expressions that pass `BivExpr.ok`, all stored rows that pass their
  guards, sizes that fit): `D` times the integral of the expression over the unit square is the
  integer `BivExpr.num`.
* `BivExpr.sq_integral_le`, `BivExpr.sq_integral_le_div` (all residual expressions and sizes
  that pass `BivExpr.sizesOk`, all cells): a passing `sqCheck` bounds `D` times the integral of
  the squared residual of the cell by a stored number, and the integral by that number divided
  by `D > 0`.

## Relations

Products are `zPack_mul` and the slot read is `zRestrict_zPack`
([PackedSignedRows](PackedSignedRows.lean)); a stored row is read with `signedGuardCheck`
([PackedLinearAlgebra](PackedLinearAlgebra.lean)). `BivExpr.integral_eq` at the expression
`mul R R` is the exact value of the squared `L²` norm of `R`; `Cond.onIcc`
([Cond](../Cert/Cond.lean)) bounds a polynomial on a cell by balls, which gives an upper bound
for the same integral after subdivision.

## Scope

The rows are polynomials on the unit square in the monomial basis; a factor that is not a
polynomial (the phase slope of a logarithmic radial phase) needs a polynomial enclosure with a
remainder. The partial derivatives are computed slot by slot.
-/

@[expose] public section

open Finset intervalIntegral

namespace CAS.Numerics

/-! ### Polynomials in two variables as coefficient rows -/

/-- The value at `(x, y)` of the polynomial whose coefficient of `x ^ (q % S) * y ^ (q / S)` is
`c q`, for the slots `q < L`. -/
def bivEval (S : ℕ) (c : ℕ → ℤ) (L : ℕ) (x y : ℝ) : ℝ :=
  ∑ q ∈ range L, (c q : ℝ) * x ^ (q % S) * y ^ (q / S)

/-- The row `c` vanishes from slot `L` on and at the slots of degree at least `n` in `x`. -/
structure BivSupp (S n L : ℕ) (c : ℕ → ℤ) : Prop where
  /-- No slot from `L` on. -/
  len : ∀ q, L ≤ q → c q = 0
  /-- No slot of degree at least `n` in `x`. -/
  deg : ∀ q, n ≤ q % S → c q = 0

/-- More slots do not change the value when the row vanishes there. -/
theorem bivEval_extend {S L L' : ℕ} {c : ℕ → ℤ} (h : L ≤ L') (hc : ∀ q, L ≤ q → c q = 0)
    (x y : ℝ) : bivEval S c L' x y = bivEval S c L x y := by
  refine (sum_subset (range_subset_range.2 h) fun q _ hq' ↦ ?_).symm
  rw [hc q (by simpa using hq')]
  simp

/-- The value of an integer multiple of a row. -/
theorem bivEval_smul (S : ℕ) (z : ℤ) (c : ℕ → ℤ) (L : ℕ) (x y : ℝ) :
    bivEval S (fun q ↦ z * c q) L x y = z * bivEval S c L x y := by
  unfold bivEval
  rw [mul_sum]
  exact sum_congr rfl fun q _ ↦ by push_cast; ring

/-- The value of a sum of rows. -/
theorem bivEval_add (S : ℕ) (c d : ℕ → ℤ) (L : ℕ) (x y : ℝ) :
    bivEval S (fun q ↦ c q + d q) L x y = bivEval S c L x y + bivEval S d L x y := by
  unfold bivEval
  rw [← sum_add_distrib]
  exact sum_congr rfl fun q _ ↦ by push_cast; ring

/-- Slots whose degrees in `x` add up to less than `S` add without a carry. -/
theorem add_mod_div_of_lt {S i j : ℕ} (hS : 0 < S) (h : i % S + j % S < S) :
    (i + j) % S = i % S + j % S ∧ (i + j) / S = i / S + j / S := by
  constructor
  · rw [Nat.add_mod, Nat.mod_eq_of_lt h]
  · rw [Nat.add_div hS, ite_eq_right (by omega), add_zero]

/-- **Products.** For a positive stride, if two rows have degrees below `n` and `n'` in `x` with
`n + n' ≤ S + 1`, so that the degrees add up to less than `S`, the convolution of the rows is the
row of the product polynomial: the degrees in `x` of two terms add without a carry into the
degree in `y`. -/
theorem bivEval_zConv {S n n' L L' : ℕ} {c d : ℕ → ℤ} (hS : 0 < S) (hc : BivSupp S n L c)
    (hd : BivSupp S n' L' d) (hn : n + n' ≤ S + 1) (x y : ℝ) :
    bivEval S (zConv L L' c d) (L + L') x y = bivEval S c L x y * bivEval S d L' x y := by
  unfold bivEval zConv
  rw [sum_mul_sum]
  have h1 : ∀ q ∈ range (L + L'),
      ((∑ i ∈ range L, ∑ j ∈ range L', if i + j = q then c i * d j else 0 : ℤ) : ℝ) *
        x ^ (q % S) * y ^ (q / S) =
      ∑ i ∈ range L, ∑ j ∈ range L',
        if i + j = q then ((c i : ℝ) * d j) * x ^ (q % S) * y ^ (q / S) else 0 := by
    intro q _
    push_cast
    rw [sum_mul, sum_mul]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [sum_mul, sum_mul]
    refine sum_congr rfl fun j _ ↦ ?_
    split_ifs <;> simp
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [sum_comm]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [sum_ite_eq (range (L + L')) (i + j) fun q ↦ ((c i : ℝ) * d j) * x ^ (q % S) * y ^ (q / S),
    ite_eq_left (mem_range.2 (by have := mem_range.1 hi; have := mem_range.1 hj; omega))]
  by_cases hci : c i = 0
  · simp [hci]
  by_cases hdj : d j = 0
  · simp [hdj]
  have hi' : i % S < n := by
    by_contra h
    exact hci (hc.deg i (not_lt.mp h))
  have hj' : j % S < n' := by
    by_contra h
    exact hdj (hd.deg j (not_lt.mp h))
  obtain ⟨hmod, hdiv⟩ := add_mod_div_of_lt (i := i) (j := j) hS (by omega)
  rw [hmod, hdiv, pow_add, pow_add]
  ring

/-- Under the hypotheses of `bivEval_zConv`, the convolution of two rows has at most `L + L'`
slots and degree below `n + n' - 1` in `x`. -/
theorem bivSupp_zConv {S n n' L L' : ℕ} {c d : ℕ → ℤ} (hS : 0 < S) (hc : BivSupp S n L c)
    (hd : BivSupp S n' L' d) (hn : n + n' ≤ S + 1) :
    BivSupp S (n + n' - 1) (L + L') (zConv L L' c d) := by
  refine ⟨fun q hq ↦ zConv_eq_zero_of_le c d (by omega), fun q hq ↦ ?_⟩
  unfold zConv
  refine sum_eq_zero fun i _ ↦ sum_eq_zero fun j _ ↦ ?_
  split_ifs with hij
  swap
  · rfl
  by_cases hci : c i = 0
  · simp [hci]
  by_cases hdj : d j = 0
  · simp [hdj]
  exfalso
  have hi' : i % S < n := by
    by_contra h
    exact hci (hc.deg i (not_lt.mp h))
  have hj' : j % S < n' := by
    by_contra h
    exact hdj (hd.deg j (not_lt.mp h))
  have := (add_mod_div_of_lt (i := i) (j := j) hS (by omega)).1
  rw [hij] at this
  omega

/-! ### Partial derivatives -/

/-- The row of the derivative in `x`: slot `q` holds `(q % S + 1) * c (q + 1)` when slot
`q + 1` is in the same block of `S` slots and below `L`. -/
def dxCoef (S L : ℕ) (c : ℕ → ℤ) (q : ℕ) : ℤ :=
  if q % S + 1 < S ∧ q + 1 < L then ((q % S + 1 : ℕ) : ℤ) * c (q + 1) else 0

/-- The row of the derivative in `y`: slot `q` holds `(q / S + 1) * c (q + S)` when slot `q + S`
is below `L`. -/
def dyCoef (S L : ℕ) (c : ℕ → ℤ) (q : ℕ) : ℤ :=
  if q + S < L then ((q / S + 1 : ℕ) : ℤ) * c (q + S) else 0

/-- The next slot of a block: the degree in `x` grows by one and the degree in `y` stays. -/
theorem succ_mod_div_of_lt {S q : ℕ} (h : q % S + 1 < S) :
    (q + 1) % S = q % S + 1 ∧ (q + 1) / S = q / S := by
  have hS : 0 < S := by omega
  have h1 : 1 % S = 1 := Nat.mod_eq_of_lt (by omega)
  obtain ⟨hm, hd⟩ := add_mod_div_of_lt (i := q) (j := 1) hS (by omega)
  rw [h1] at hm
  rw [Nat.div_eq_of_lt (by omega : 1 < S), add_zero] at hd
  exact ⟨hm, hd⟩

/-- The derivative row in `x` keeps the support. -/
theorem bivSupp_dxCoef {S n L : ℕ} {c : ℕ → ℤ} (hc : BivSupp S n L c) :
    BivSupp S n L (dxCoef S L c) := by
  refine ⟨fun q hq ↦ ite_eq_right fun h ↦ by omega, fun q hq ↦ ?_⟩
  unfold dxCoef
  split_ifs with h
  · rw [hc.deg (q + 1) (by rw [(succ_mod_div_of_lt h.1).1]; omega), mul_zero]
  · rfl

/-- The derivative row in `y` keeps the support. -/
theorem bivSupp_dyCoef {S n L : ℕ} {c : ℕ → ℤ} (hc : BivSupp S n L c) :
    BivSupp S n L (dyCoef S L c) := by
  refine ⟨fun q hq ↦ ite_eq_right fun h ↦ by omega, fun q hq ↦ ?_⟩
  unfold dyCoef
  split_ifs with h
  · rw [hc.deg (q + S) (by rw [Nat.add_mod_right]; exact hq), mul_zero]
  · rfl

/-- **The derivative in `x`.** For a positive stride, the polynomial of the row `dxCoef S L c` is
the derivative in `x` of the polynomial of the row `c`, at every point. -/
theorem hasDerivAt_bivEval_x {S : ℕ} (hS : 0 < S) (L : ℕ) (c : ℕ → ℤ) (x y : ℝ) :
    HasDerivAt (fun t ↦ bivEval S c L t y) (bivEval S (dxCoef S L c) L x y) x := by
  have hterm : ∀ q ∈ range L, HasDerivAt (fun t : ℝ ↦ (c q : ℝ) * t ^ (q % S) * y ^ (q / S))
      ((c q : ℝ) * ((q % S : ℕ) * x ^ (q % S - 1)) * y ^ (q / S)) x := fun q _ ↦
    ((hasDerivAt_pow (q % S) x).const_mul (c q : ℝ)).mul_const (y ^ (q / S))
  have hsum := HasDerivAt.fun_sum hterm
  have heq : ∑ q ∈ range L, (c q : ℝ) * ((q % S : ℕ) * x ^ (q % S - 1)) * y ^ (q / S) =
      bivEval S (dxCoef S L c) L x y := by
    unfold bivEval
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · simp
    obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
    rw [sum_range_succ', sum_range_succ]
    have h0 : (c 0 : ℝ) * (((0 % S : ℕ) : ℝ) * x ^ (0 % S - 1)) * y ^ (0 / S) = 0 := by simp
    have hm : ((dxCoef S (m + 1) c m : ℤ) : ℝ) * x ^ (m % S) * y ^ (m / S) = 0 := by
      rw [dxCoef, ite_eq_right (by omega)]
      simp
    rw [h0, hm, add_zero, add_zero]
    refine sum_congr rfl fun q hq ↦ ?_
    have hq' := mem_range.mp hq
    by_cases h : q % S + 1 < S
    · obtain ⟨hmod, hdiv⟩ := succ_mod_div_of_lt h
      rw [dxCoef, ite_eq_left ⟨h, by omega⟩, hmod, hdiv, Nat.add_sub_cancel, Int.cast_mul,
        Int.cast_natCast]
      ring
    · -- The next slot starts a block: its degree in `x` is zero.
      have hzero : (q + 1) % S = 0 := by
        have hlt := Nat.mod_lt q hS
        have hq1 : q + 1 = S * (q / S + 1) := by
          have := Nat.div_add_mod q S
          rw [Nat.mul_add, Nat.mul_one]
          omega
        rw [hq1, Nat.mul_mod_right]
      rw [dxCoef, ite_eq_right (fun hh ↦ h hh.1), hzero]
      simp
  rw [heq] at hsum
  exact hsum

/-- **The derivative in `y`.** For a positive stride, the polynomial of the row `dyCoef S L c` is
the derivative in `y` of the polynomial of the row `c`, at every point. -/
theorem hasDerivAt_bivEval_y {S : ℕ} (hS : 0 < S) (L : ℕ) (c : ℕ → ℤ) (x y : ℝ) :
    HasDerivAt (fun t ↦ bivEval S c L x t) (bivEval S (dyCoef S L c) L x y) y := by
  have hterm : ∀ q ∈ range L, HasDerivAt (fun t : ℝ ↦ (c q : ℝ) * x ^ (q % S) * t ^ (q / S))
      ((c q : ℝ) * x ^ (q % S) * ((q / S : ℕ) * y ^ (q / S - 1))) y := fun q _ ↦
    (hasDerivAt_pow (q / S) y).const_mul ((c q : ℝ) * x ^ (q % S))
  have hsum := HasDerivAt.fun_sum hterm
  have heq : ∑ q ∈ range L, (c q : ℝ) * x ^ (q % S) * ((q / S : ℕ) * y ^ (q / S - 1)) =
      bivEval S (dyCoef S L c) L x y := by
    unfold bivEval
    rcases le_or_gt L S with hLS | hLS
    · -- No slot has positive degree in `y`.
      rw [sum_eq_zero fun q hq ↦ by
        rw [Nat.div_eq_of_lt (by have := mem_range.mp hq; omega)]; simp,
        sum_eq_zero fun q _ ↦ by rw [dyCoef, ite_eq_right (by omega)]; simp]
    obtain ⟨m, rfl⟩ : ∃ m, L = S + m := ⟨L - S, by omega⟩
    rw [sum_range_add, sum_eq_zero fun q hq ↦ by
      rw [Nat.div_eq_of_lt (mem_range.mp hq)]; simp, zero_add, Nat.add_comm S m, sum_range_add,
      sum_eq_zero (s := range S) fun q _ ↦ by rw [dyCoef, ite_eq_right (by omega)]; simp,
      add_zero]
    refine sum_congr rfl fun q hq ↦ ?_
    have hq' := mem_range.mp hq
    rw [dyCoef, ite_eq_left (by omega), Nat.add_mod_left, Nat.add_div_left q hS,
      Nat.add_comm q S, Nat.add_sub_cancel, Int.cast_mul, Int.cast_natCast]
    ring
  rw [heq] at hsum
  exact hsum

/-! ### The integral over the unit square -/

/-- **The integral over the unit square.** The polynomial of a row `c` of `L` slots has the
integral `∑ q < L, c q / ((q % S + 1) (q / S + 1))`, since `x ^ i y ^ j` has the integral
`1 / ((i + 1) (j + 1))`. -/
theorem integral_bivEval (S : ℕ) (c : ℕ → ℤ) (L : ℕ) :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, bivEval S c L x y =
      ∑ q ∈ range L, (c q : ℝ) / (((q % S + 1 : ℕ) : ℝ) * ((q / S + 1 : ℕ) : ℝ)) := by
  have hin : ∀ x : ℝ, ∫ y in (0 : ℝ)..1, bivEval S c L x y =
      ∑ q ∈ range L, (c q : ℝ) / ((q / S + 1 : ℕ) : ℝ) * x ^ (q % S) := by
    intro x
    unfold bivEval
    rw [integral_finsetSum fun q _ ↦ Continuous.intervalIntegrable (by fun_prop) _ _]
    refine sum_congr rfl fun q _ ↦ ?_
    rw [integral_const_mul, integral_pow]
    push_cast
    simp only [one_pow, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
      zero_pow, sub_zero]
    ring
  simp_rw [hin]
  rw [integral_finsetSum fun q _ ↦ Continuous.intervalIntegrable (by fun_prop) _ _]
  refine sum_congr rfl fun q _ ↦ ?_
  rw [integral_const_mul, integral_pow]
  push_cast
  simp only [one_pow, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
    zero_pow, sub_zero]
  have h1 : ((q % S : ℕ) : ℝ) + 1 ≠ 0 := by positivity
  have h2 : ((q / S : ℕ) : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-! ### Expressions -/

/-- Polynomial expressions in two variables: stored rows, integer multiples, sums, products and
the two partial derivatives. -/
inductive BivExpr where
  /-- The stored row `k`. -/
  | var (k : ℕ)
  /-- An integer multiple. -/
  | smul (z : ℤ) (e : BivExpr)
  /-- A sum. -/
  | add (e f : BivExpr)
  /-- A product. -/
  | mul (e f : BivExpr)
  /-- The derivative in `x`. -/
  | dx (e : BivExpr)
  /-- The derivative in `y`. -/
  | dy (e : BivExpr)

namespace BivExpr

/-- The number of slots of the row of an expression, for stored rows of `L` slots. -/
def len (L : ℕ) : BivExpr → ℕ
  | var _ => L
  | smul _ e => len L e
  | add e f => Nat.max (len L e) (len L f)
  | mul e f => Nat.add (len L e) (len L f)
  | dx e => len L e
  | dy e => len L e

/-- A bound for the degree in `x`, plus one, for stored rows of degree below `n` in `x`. -/
def degX (n : ℕ) : BivExpr → ℕ
  | var _ => n
  | smul _ e => degX n e
  | add e f => Nat.max (degX n e) (degX n f)
  | mul e f => Nat.sub (Nat.add (degX n e) (degX n f)) 1
  | dx e => degX n e
  | dy e => degX n e

/-- The coefficient row of an expression, from the coefficient rows `cenv k` of the stored
rows. -/
def coef (S L : ℕ) (cenv : ℕ → ℕ → ℤ) : BivExpr → ℕ → ℤ
  | var k => cenv k
  | smul z e => fun q ↦ z * coef S L cenv e q
  | add e f => fun q ↦ coef S L cenv e q + coef S L cenv f q
  | mul e f => zConv (len L e) (len L f) (coef S L cenv e) (coef S L cenv f)
  | dx e => dxCoef S (len L e) (coef S L cenv e)
  | dy e => dyCoef S (len L e) (coef S L cenv e)

/-- A bound for the absolute values of the coefficients, for stored coefficients bounded by
`B`. -/
def bnd (S L B : ℕ) : BivExpr → ℕ
  | var _ => B
  | smul z e => Nat.mul z.natAbs (bnd S L B e)
  | add e f => Nat.add (bnd S L B e) (bnd S L B f)
  | mul e f => Nat.mul (len L e) (Nat.mul (bnd S L B e) (bnd S L B f))
  | dx e => Nat.mul S (bnd S L B e)
  | dy e => Nat.mul (len L e) (bnd S L B e)

/-- The test of an expression: at every product the bounds `degX` of the two factors add up to at
most `S + 1`, and under every derivative the bound `bnd` of the coefficients is below
`2 ^ (W - 1)`, so that they fit a slot of `W` bits. -/
def ok (W S n L B : ℕ) : BivExpr → Bool
  | var _ => true
  | smul _ e => ok W S n L B e
  | add e f => ok W S n L B e && ok W S n L B f
  | mul e f => ok W S n L B e && ok W S n L B f &&
      Nat.ble (Nat.add (degX n e) (degX n f)) (Nat.add S 1)
  | dx e => ok W S n L B e && Nat.blt (bnd S L B e) (Nat.shiftLeft 1 (Nat.sub W 1))
  | dy e => ok W S n L B e && Nat.blt (bnd S L B e) (Nat.shiftLeft 1 (Nat.sub W 1))

/-- The real function of an expression: the stored rows are polynomials, and `dx`, `dy` are the
partial derivatives. -/
noncomputable def eval (S L : ℕ) (cenv : ℕ → ℕ → ℤ) : BivExpr → ℝ → ℝ → ℝ
  | var k => bivEval S (cenv k) L
  | smul z e => fun x y ↦ z * eval S L cenv e x y
  | add e f => fun x y ↦ eval S L cenv e x y + eval S L cenv f x y
  | mul e f => fun x y ↦ eval S L cenv e x y * eval S L cenv f x y
  | dx e => fun x y ↦ deriv (fun t ↦ eval S L cenv e t y) x
  | dy e => fun x y ↦ deriv (fun t ↦ eval S L cenv e x t) y

variable {W S n L B : ℕ} {cenv : ℕ → ℕ → ℤ}

/-- For a positive stride and stored rows with `BivSupp S n L`, the coefficient row of an
expression that passes its test has the support that `len` and `degX` state. -/
theorem bivSupp_coef (hS : 0 < S) (hvars : ∀ k, BivSupp S n L (cenv k)) :
    ∀ e : BivExpr, ok W S n L B e = true →
      BivSupp S (degX n e) (len L e) (coef S L cenv e) := by
  intro e
  induction e with
  | var k => exact fun _ ↦ hvars k
  | smul z e ih =>
    intro h
    exact ⟨fun q hq ↦ by change z * _ = 0; rw [(ih h).len q hq, mul_zero],
      fun q hq ↦ by change z * _ = 0; rw [(ih h).deg q hq, mul_zero]⟩
  | add e f ihe ihf =>
    intro h
    simp only [ok, Bool.and_eq_true] at h
    have he := ihe h.1
    have hf := ihf h.2
    refine ⟨fun q hq ↦ ?_, fun q hq ↦ ?_⟩
    · have hq' : max (len L e) (len L f) ≤ q := hq
      change coef S L cenv e q + coef S L cenv f q = 0
      rw [he.len q (by omega), hf.len q (by omega), add_zero]
    · have hq' : max (degX n e) (degX n f) ≤ q % S := hq
      change coef S L cenv e q + coef S L cenv f q = 0
      rw [he.deg q (by omega), hf.deg q (by omega), add_zero]
  | mul e f ihe ihf =>
    intro h
    simp only [ok, Bool.and_eq_true, Nat.ble_eq] at h
    exact bivSupp_zConv hS (ihe h.1.1) (ihf h.1.2) h.2
  | dx e ih =>
    intro h
    simp only [ok, Bool.and_eq_true] at h
    exact bivSupp_dxCoef (ih h.1)
  | dy e ih =>
    intro h
    simp only [ok, Bool.and_eq_true] at h
    exact bivSupp_dyCoef (ih h.1)

/-- **The value of an expression is the polynomial of its coefficient row.** This holds for a
positive stride, stored rows with `BivSupp S n L` and every expression that passes `ok`: sums and
integer multiples act slot by slot, products are `bivEval_zConv`, and the partial derivatives are
`hasDerivAt_bivEval_x` and `hasDerivAt_bivEval_y`. -/
theorem eval_eq (hS : 0 < S) (hvars : ∀ k, BivSupp S n L (cenv k)) :
    ∀ e : BivExpr, ok W S n L B e = true →
      ∀ x y, eval S L cenv e x y = bivEval S (coef S L cenv e) (len L e) x y := by
  intro e
  induction e with
  | var k => exact fun _ _ _ ↦ rfl
  | smul z e ih =>
    intro h x y
    change z * eval S L cenv e x y = bivEval S (fun q ↦ z * coef S L cenv e q) (len L e) x y
    rw [bivEval_smul, ih h]
  | add e f ihe ihf =>
    intro h x y
    have h' := h
    simp only [ok, Bool.and_eq_true] at h'
    have he := bivSupp_coef (W := W) (B := B) hS hvars e h'.1
    have hf := bivSupp_coef (W := W) (B := B) hS hvars f h'.2
    change eval S L cenv e x y + eval S L cenv f x y =
      bivEval S (fun q ↦ coef S L cenv e q + coef S L cenv f q)
        (max (len L e) (len L f)) x y
    rw [bivEval_add, bivEval_extend (le_max_left _ _) he.len,
      bivEval_extend (le_max_right _ _) hf.len, ihe h'.1, ihf h'.2]
  | mul e f ihe ihf =>
    intro h x y
    have h' := h
    simp only [ok, Bool.and_eq_true, Nat.ble_eq] at h'
    have he := bivSupp_coef (W := W) (B := B) hS hvars e h'.1.1
    have hf := bivSupp_coef (W := W) (B := B) hS hvars f h'.1.2
    change eval S L cenv e x y * eval S L cenv f x y =
      bivEval S (zConv (len L e) (len L f) (coef S L cenv e) (coef S L cenv f))
        (len L e + len L f) x y
    rw [bivEval_zConv hS he hf h'.2, ihe h'.1.1, ihf h'.1.2]
  | dx e ih =>
    intro h x y
    simp only [ok, Bool.and_eq_true] at h
    have hfun : (fun t ↦ eval S L cenv e t y) =
        fun t ↦ bivEval S (coef S L cenv e) (len L e) t y := funext fun t ↦ ih h.1 t y
    change deriv (fun t ↦ eval S L cenv e t y) x = _
    rw [hfun]
    exact (hasDerivAt_bivEval_x hS (len L e) (coef S L cenv e) x y).deriv
  | dy e ih =>
    intro h x y
    simp only [ok, Bool.and_eq_true] at h
    have hfun : (fun t ↦ eval S L cenv e x t) =
        fun t ↦ bivEval S (coef S L cenv e) (len L e) x t := funext fun t ↦ ih h.1 x t
    change deriv (fun t ↦ eval S L cenv e x t) y = _
    rw [hfun]
    exact (hasDerivAt_bivEval_y hS (len L e) (coef S L cenv e) x y).deriv

/-- When the stored coefficients are bounded by `B`, the coefficients of an expression are bounded
by `bnd`. -/
theorem abs_coef_le (hB : ∀ k q, |cenv k q| ≤ B) :
    ∀ (e : BivExpr) (q : ℕ), |coef S L cenv e q| ≤ (bnd S L B e : ℤ) := by
  intro e
  induction e with
  | var k => exact fun q ↦ hB k q
  | smul z e ih =>
    intro q
    change |z * coef S L cenv e q| ≤ ((z.natAbs * bnd S L B e : ℕ) : ℤ)
    rw [abs_mul, Nat.cast_mul, Int.natCast_natAbs]
    exact mul_le_mul_of_nonneg_left (ih q) (abs_nonneg z)
  | add e f ihe ihf =>
    intro q
    change |coef S L cenv e q + coef S L cenv f q| ≤ ((bnd S L B e + bnd S L B f : ℕ) : ℤ)
    rw [Nat.cast_add]
    exact (abs_add_le _ _).trans (add_le_add (ihe q) (ihf q))
  | mul e f ihe ihf =>
    intro q
    change |zConv (len L e) (len L f) (coef S L cenv e) (coef S L cenv f) q| ≤
      ((len L e * (bnd S L B e * bnd S L B f) : ℕ) : ℤ)
    have := abs_zConv_le' (n := len L e) (m := len L f) (Int.natCast_nonneg (bnd S L B f)) ihe ihf q
    exact_mod_cast this
  | dx e ih =>
    intro q
    change |dxCoef S (len L e) (coef S L cenv e) q| ≤ ((S * bnd S L B e : ℕ) : ℤ)
    unfold dxCoef
    split_ifs with h
    · rw [abs_mul, Nat.abs_cast, Nat.cast_mul]
      exact mul_le_mul (by exact_mod_cast h.1.le) (ih _) (abs_nonneg _) (Int.natCast_nonneg _)
    · rw [abs_zero]
      exact Int.natCast_nonneg _
  | dy e ih =>
    intro q
    change |dyCoef S (len L e) (coef S L cenv e) q| ≤ ((len L e * bnd S L B e : ℕ) : ℤ)
    unfold dyCoef
    split_ifs with h
    · rw [abs_mul, Nat.abs_cast, Nat.cast_mul]
      refine mul_le_mul ?_ (ih _) (abs_nonneg _) (Int.natCast_nonneg _)
      have : q / S + 1 ≤ len L e := by
        have := Nat.div_le_self q S
        omega
      exact_mod_cast this
    · rw [abs_zero]
      exact Int.natCast_nonneg _

end BivExpr

/-! ### Packed rows -/

/-- A linear map of the slots of a biased row: the sum over the slots `q < L` with `use q` of
`g q` times slot `src q` of `Y`, placed at slot `q`. The bias of `Y` is not removed here. -/
def slotComb (W L : ℕ) (g src : ℕ → ℕ) (use : ℕ → Bool) (Y : ℕ) : ℕ :=
  natSum L fun q ↦
    cond (use q) (Nat.shiftLeft (Nat.mul (g q) (slot W (src q) Y)) (Nat.mul W q)) 0

/-- The same map on a signed row: the map of the biased row minus the map of the bias row. -/
def zSlotComb (W L : ℕ) (g src : ℕ → ℕ) (use : ℕ → Bool) (X : ℤ) : ℤ :=
  Int.sub (Int.ofNat (slotComb W L g src use (Int.toNat (Int.add X (zBias W L)))))
    (Int.ofNat (slotComb W L g src use (Int.toNat (zBias W L))))

/-- **A linear map of the slots of a signed row.** For a row of entries that fit, with
`src q < L` wherever `use q`, slot `q` of `zSlotComb` is `g q * c (src q)` where `use q`, and `0`
elsewhere. -/
theorem zSlotComb_zPack {W L : ℕ} (hW : 0 < W) {c : ℕ → ℤ} (h : ZFits W L c) {g src : ℕ → ℕ}
    {use : ℕ → Bool} (hsrc : ∀ q < L, use q = true → src q < L) :
    zSlotComb W L g src use (zPack W L c) =
      zPack W L fun q ↦ if use q = true then (g q : ℤ) * c (src q) else 0 := by
  have hpow := pow_sub_one_mul hW.ne' (2 : ℕ)
  have hbias : Int.toNat (zBias W L) = packSlots W L fun _ ↦ 2 ^ (W - 1) := by
    rw [zBias, Int.ofNat_eq_natCast, Int.toNat_natCast]
    exact constSlots_eq hW L _
  have hslotB : ∀ k < L, slot W k (packSlots W L fun _ ↦ 2 ^ (W - 1)) = 2 ^ (W - 1) := by
    intro k hk
    rw [slot_packed_eq (fun _ _ ↦ Nat.pow_lt_pow_right (by norm_num) (by omega)), ite_eq_left hk]
  have hslotY : ∀ k < L, slot W k (packSlots W L fun q ↦ (c q + 2 ^ (W - 1)).toNat) =
      (c k + 2 ^ (W - 1)).toNat := by
    intro k hk
    rw [slot_packed_eq (toNat_slots_lt hW h), ite_eq_left hk]
  unfold zSlotComb slotComb
  rw [zPack_biased_toNat hW h, hbias, natSum_eq_sum, natSum_eq_sum, zPack]
  change ((∑ q ∈ range L, _ : ℕ) : ℤ) - ((∑ q ∈ range L, _ : ℕ) : ℤ) = _
  rw [Nat.cast_sum, Nat.cast_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun q hq ↦ ?_
  have hq' := mem_range.mp hq
  cases hu : use q with
  | false => simp
  | true =>
    have hs := hsrc q hq' hu
    have hnn : 0 ≤ c (src q) + 2 ^ (W - 1) := by linarith [(h (src q) hs).1]
    simp only [Bool.cond_true, eq_self, ↓reduceIte]
    change (((g q * slot W (src q) _) <<< (W * q) : ℕ) : ℤ) -
      (((g q * slot W (src q) _) <<< (W * q) : ℕ) : ℤ) = _
    rw [hslotY _ hs, hslotB _ hs, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    push_cast
    rw [Int.toNat_of_nonneg hnn]
    ring

/-- The integer of a stored biased row. -/
def rowOfNat (W L Y : ℕ) : ℤ := Int.sub (Int.ofNat Y) (zBias W L)

/-- The coefficients of a stored biased row: its signed slots below `L`. -/
def rowCoef (W L Y : ℕ) (q : ℕ) : ℤ := if q < L then signedSlot W q Y else 0

/-- **Reading a stored row.** If the guard of a biased row passes, the row is the packed row of
its signed slots, and every slot is at most `slotBias g` in absolute value. -/
theorem rowOfNat_eq {W L g Y : ℕ} (hg : g < W) (h : signedGuardCheck W g L Y = true) :
    rowOfNat W L Y = zPack W L (rowCoef W L Y) ∧ ∀ q, |rowCoef W L Y q| ≤ (slotBias g : ℤ) := by
  have hW : 0 < W := by omega
  constructor
  · change (Y : ℤ) - zBias W L = _
    rw [cast_eq_sum_signedSlot (lt_of_signedGuardCheck h), zBias_eq hW, ← sum_sub_distrib, zPack]
    refine sum_congr rfl fun q hq ↦ ?_
    have hb : (slotBias W : ℤ) = 2 ^ (W - 1) := by
      rw [slotBias_eq, ← pow_sub_one_mul hW.ne', Nat.mul_div_cancel _ two_pos]
      push_cast
      rfl
    rw [rowCoef, ite_eq_left (mem_range.mp hq), hb]
    ring
  · intro q
    unfold rowCoef
    split_ifs with hq
    · rw [Int.abs_eq_natAbs]
      exact_mod_cast natAbs_signedSlot_le_of_signedGuardCheck hg h hq
    · simp

/-- The test that the slots of degree at least `n` in `x` of a stored row are zero: on the
slots of the mask `P` the row agrees with the bias row. -/
def padCheck (W L P Y : ℕ) : Bool := Nat.beq (Nat.land Y P) (Nat.land (biasRow W L) P)

/-- If `P` has a full slot wherever the degree in `x` is at least `n`, a passing `padCheck`
gives the support of the coefficients. -/
theorem bivSupp_rowCoef {W S n L P Y : ℕ}
    (hP : ∀ q < L, n ≤ q % S → slot W q P = slotMask W) (h : padCheck W L P Y = true) :
    BivSupp S n L (rowCoef W L Y) := by
  refine ⟨fun q hq ↦ ite_eq_right (by omega), fun q hq ↦ ?_⟩
  unfold rowCoef
  split_ifs with hqL
  swap
  · rfl
  have hland : Nat.land Y P = Nat.land (biasRow W L) P := Nat.beq_eq.mp h
  have h1 := congrArg (slot W q) hland
  rw [slot_land, slot_land, hP q hqL hq] at h1
  have hmask : ∀ v, v < 2 ^ W → Nat.land v (slotMask W) = v := fun v hv ↦ by
    change v &&& slotMask W = v
    rw [slotMask_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hv]
  rw [hmask _ (slot_lt W q Y), hmask _ (slot_lt W q _)] at h1
  rw [signedSlot, h1, biasRow_eq_packSlots, slot_packed_eq (fun _ _ ↦ slotBias_lt W),
    ite_eq_left hqL, sub_self]

namespace BivExpr

/-- The integer of an expression, computed from the integers `env k` of the stored rows: sums
and products of integers, and `zSlotComb` for the partial derivatives. -/
def pack (W S L : ℕ) (env : ℕ → ℤ) : BivExpr → ℤ
  | var k => env k
  | smul z e => Int.mul z (pack W S L env e)
  | add e f => Int.add (pack W S L env e) (pack W S L env f)
  | mul e f => Int.mul (pack W S L env e) (pack W S L env f)
  | dx e => zSlotComb W (len L e) (fun q ↦ Nat.add (Nat.mod q S) 1) (fun q ↦ Nat.add q 1)
      (fun q ↦ Nat.blt (Nat.add (Nat.mod q S) 1) S && Nat.blt (Nat.add q 1) (len L e))
      (pack W S L env e)
  | dy e => zSlotComb W (len L e) (fun q ↦ Nat.add (Nat.div q S) 1) (fun q ↦ Nat.add q S)
      (fun q ↦ Nat.blt (Nat.add q S) (len L e)) (pack W S L env e)

variable {W S n L B : ℕ} {cenv : ℕ → ℕ → ℤ} {env : ℕ → ℤ}

/-- **The integer of an expression is its packed coefficient row.** This holds for a positive
stride and width, stored rows with `BivSupp S n L` and coefficients bounded by `B`, integers
`env k` that are their packed rows, and every expression that passes `ok`. -/
theorem pack_eq (hS : 0 < S) (hW : 0 < W) (hvars : ∀ k, BivSupp S n L (cenv k))
    (hB : ∀ k q, |cenv k q| ≤ B) (henv : ∀ k, env k = zPack W L (cenv k)) :
    ∀ e : BivExpr, ok W S n L B e = true →
      pack W S L env e = zPack W (len L e) (coef S L cenv e) := by
  intro e
  induction e with
  | var k => exact fun _ ↦ henv k
  | smul z e ih =>
    intro h
    change z * pack W S L env e = zPack W (len L e) fun q ↦ z * coef S L cenv e q
    rw [ih h, zPack_smul]
  | add e f ihe ihf =>
    intro h
    have h' := h
    simp only [ok, Bool.and_eq_true] at h'
    have he := bivSupp_coef (W := W) (B := B) hS hvars e h'.1
    have hf := bivSupp_coef (W := W) (B := B) hS hvars f h'.2
    change pack W S L env e + pack W S L env f =
      zPack W (max (len L e) (len L f)) fun q ↦ coef S L cenv e q + coef S L cenv f q
    rw [← zPack_add, zPack_extend (le_max_left _ _) fun q hq _ ↦ he.len q hq,
      zPack_extend (le_max_right _ _) fun q hq _ ↦ hf.len q hq, ihe h'.1, ihf h'.2]
  | mul e f ihe ihf =>
    intro h
    have h' := h
    simp only [ok, Bool.and_eq_true] at h'
    change pack W S L env e * pack W S L env f =
      zPack W (len L e + len L f) (zConv (len L e) (len L f) (coef S L cenv e) (coef S L cenv f))
    rw [ihe h'.1.1, ihf h'.1.2, zPack_mul]
  | dx e ih =>
    intro h
    simp only [ok, Bool.and_eq_true, Nat.blt_eq] at h
    have hfit : ZFits W (len L e) (coef S L cenv e) := by
      have hb : (bnd S L B e : ℤ) < 2 ^ (W - 1) := by
        have := h.2
        change bnd S L B e < 1 <<< (W - 1) at this
        rw [Nat.one_shiftLeft] at this
        exact_mod_cast this
      intro q _
      have := abs_le.mp (abs_coef_le (S := S) (L := L) hB e q)
      constructor <;> linarith
    change zSlotComb W (len L e) _ _ _ (pack W S L env e) =
      zPack W (len L e) (dxCoef S (len L e) (coef S L cenv e))
    rw [ih h.1, zSlotComb_zPack hW hfit fun q _ hu ↦ by
      simp only [Bool.and_eq_true, Nat.blt_eq] at hu
      exact hu.2]
    refine zPack_congr fun q _ ↦ ?_
    simp only [Bool.and_eq_true, Nat.blt_eq, dxCoef]
    rfl
  | dy e ih =>
    intro h
    simp only [ok, Bool.and_eq_true, Nat.blt_eq] at h
    have hfit : ZFits W (len L e) (coef S L cenv e) := by
      have hb : (bnd S L B e : ℤ) < 2 ^ (W - 1) := by
        have := h.2
        change bnd S L B e < 1 <<< (W - 1) at this
        rw [Nat.one_shiftLeft] at this
        exact_mod_cast this
      intro q _
      have := abs_le.mp (abs_coef_le (S := S) (L := L) hB e q)
      constructor <;> linarith
    change zSlotComb W (len L e) _ _ _ (pack W S L env e) =
      zPack W (len L e) (dyCoef S (len L e) (coef S L cenv e))
    rw [ih h.1, zSlotComb_zPack hW hfit fun q _ hu ↦ by
      simp only [Nat.blt_eq] at hu
      exact hu]
    refine zPack_congr fun q _ ↦ ?_
    simp only [Nat.blt_eq, dyCoef]
    rfl

end BivExpr

/-! ### The integral as one slot of a product -/

/-- The integer `D / ((q % S + 1) * (q / S + 1))`: `D` times the integral of the monomial of
slot `q` over the unit square, when the division is exact. -/
def moment (S D q : ℕ) : ℕ :=
  Nat.div D (Nat.mul (Nat.add (Nat.mod q S) 1) (Nat.add (Nat.div q S) 1))

/-- The packed row of the moments of the slots `ℓ - 1, …, 0`, in this order. -/
def momentRow (W S D ℓ : ℕ) : ℕ := packSlots W ℓ fun j ↦ moment S D (Nat.sub (Nat.sub ℓ 1) j)

/-- `D` is a multiple of the denominator of every slot below `ℓ`. -/
def momentOk (S D ℓ : ℕ) : Bool :=
  natAll ℓ fun q ↦
    Nat.beq (Nat.mod D (Nat.mul (Nat.add (Nat.mod q S) 1) (Nat.add (Nat.div q S) 1))) 0

/-- Slot `ℓ - 1` of the product of a row of `ℓ` slots with the row `M` of the moments. -/
def momentNum (W ℓ : ℕ) (X : ℤ) (M : ℕ) : ℤ :=
  zRestrict W (Nat.add ℓ ℓ) (Nat.sub ℓ 1) 1 (Int.mul X (Int.ofNat M))

/-- **One slot of a product is `D` times the integral.** Let `c` be a row of `ℓ > 0` slots with
`|c q| ≤ b`, `D` a multiple of the denominators (`momentOk`), `W > 0` and `2 ℓ b D < 2 ^ W`. Then
the slot `ℓ - 1` of the product of the packed row with the reversed row of the moments is
`D ∑ q < ℓ, c q / ((q % S + 1) (q / S + 1))`. -/
theorem momentNum_eq {W S D ℓ b : ℕ} {c : ℕ → ℤ} (hW : 0 < W) (hℓ : 0 < ℓ)
    (hc : ∀ q, |c q| ≤ b) (hD : momentOk S D ℓ = true)
    (hfit : 2 * (ℓ * (b * D)) < 2 ^ W) :
    ((momentNum W ℓ (zPack W ℓ c) (momentRow W S D ℓ) : ℤ) : ℝ) =
      D * ∑ q ∈ range ℓ, (c q : ℝ) / (((q % S + 1 : ℕ) : ℝ) * ((q / S + 1 : ℕ) : ℝ)) := by
  set μ : ℕ → ℤ := fun j ↦ (moment S D (ℓ - 1 - j) : ℤ) with hμ
  have hM : ((momentRow W S D ℓ : ℕ) : ℤ) = zPack W ℓ μ := by
    rw [momentRow, packSlots_eq_sum, zPack]
    push_cast
    rfl
  have hμb : ∀ j, |μ j| ≤ (D : ℤ) := fun j ↦ by
    rw [hμ, Nat.abs_cast]
    exact_mod_cast Nat.div_le_self D _
  have hconv : ∀ q, |zConv ℓ ℓ c μ q| ≤ ((ℓ * (b * D) : ℕ) : ℤ) := fun q ↦ by
    have := abs_zConv_le' (n := ℓ) (m := ℓ) (Int.natCast_nonneg D) hc hμb q
    exact_mod_cast this
  have hfits : ZFits W (ℓ + ℓ) (zConv ℓ ℓ c μ) := by
    have hpow := pow_sub_one_mul hW.ne' (2 : ℕ)
    have hlt : ((ℓ * (b * D) : ℕ) : ℤ) < 2 ^ (W - 1) := by
      have : ℓ * (b * D) < 2 ^ (W - 1) := by omega
      exact_mod_cast this
    intro q _
    have := abs_le.mp (hconv q)
    constructor <;> linarith
  have hslot : momentNum W ℓ (zPack W ℓ c) (momentRow W S D ℓ) = zConv ℓ ℓ c μ (ℓ - 1) := by
    unfold momentNum
    change zRestrict W (ℓ + ℓ) (ℓ - 1) 1 (zPack W ℓ c * ((momentRow W S D ℓ : ℕ) : ℤ)) = _
    rw [hM, zPack_mul, zRestrict_zPack hW hfits (by omega)]
    simp [zPack]
  have hval : zConv ℓ ℓ c μ (ℓ - 1) = ∑ i ∈ range ℓ, c i * (moment S D i : ℤ) := by
    unfold zConv
    refine sum_congr rfl fun i hi ↦ ?_
    have hi' := mem_range.mp hi
    have hcond : ∀ j ∈ range ℓ, (if i + j = ℓ - 1 then c i * μ j else 0) =
        if ℓ - 1 - i = j then c i * μ j else 0 := fun j _ ↦ by
      by_cases hj : i + j = ℓ - 1
      · rw [ite_eq_left hj, ite_eq_left (by omega)]
      · rw [ite_eq_right hj, ite_eq_right (by omega)]
    rw [sum_congr rfl hcond, sum_ite_eq (range ℓ) (ℓ - 1 - i) fun j ↦ c i * μ j,
      ite_eq_left (mem_range.2 (by omega)), hμ]
    have : ℓ - 1 - (ℓ - 1 - i) = i := by omega
    simp only [this]
  rw [hslot, hval, mul_sum, Int.cast_sum]
  refine sum_congr rfl fun q hq ↦ ?_
  have hq' := mem_range.mp hq
  have hdvd : D % ((q % S + 1) * (q / S + 1)) = 0 := by
    have := natAll_spec hD hq'
    exact Nat.beq_eq.mp this
  have hden : ((q % S + 1 : ℕ) : ℝ) * ((q / S + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hmul : ((moment S D q : ℕ) : ℝ) * (((q % S + 1 : ℕ) : ℝ) * ((q / S + 1 : ℕ) : ℝ)) = D := by
    have h1 : moment S D q * ((q % S + 1) * (q / S + 1)) = D :=
      Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdvd)
    exact_mod_cast h1
  have hmoment : ((moment S D q : ℕ) : ℝ) =
      D / (((q % S + 1 : ℕ) : ℝ) * ((q / S + 1 : ℕ) : ℝ)) := by
    rw [eq_div_iff hden]
    exact hmul
  rw [Int.cast_mul, Int.cast_natCast, hmoment]
  ring

namespace BivExpr

variable {W S n L B D : ℕ}

/-- The integer that `integral_eq` identifies with `D` times the integral of the expression:
one slot of the product of the integer of the expression with the row `M` of the moments. -/
def num (W S L : ℕ) (env : ℕ → ℤ) (M : ℕ) (e : BivExpr) : ℤ :=
  momentNum W (len L e) (pack W S L env e) M

/-- **The exact integral of an expression.** For a positive stride, let the stored rows `Y k`
pass their guards (slots bounded by `slotBias g ≤ B` with `g < W`, zero slots where the degree in
`x` is at least `n`), let the expression `e` pass its test with `len e > 0`, let `D` be a multiple
of the denominators below `len e`, and let `2 (len e) (bnd e) D < 2 ^ W`. Then `D` times the
integral over the unit square of the real function of `e` is the integer `num e`, computed from
the stored rows by sums, products and slot maps of integers and one slot read.

With `e = mul R R` this is the exact value of the squared `L²` norm of the residual `R` on one
cell. -/
theorem integral_eq {g P : ℕ} {Y : ℕ → ℕ} (hS : 0 < S) (hg : g < W) (hgB : slotBias g ≤ B)
    (hguard : ∀ k, signedGuardCheck W g L (Y k) = true)
    (hP : ∀ q < L, n ≤ q % S → slot W q P = slotMask W)
    (hpad : ∀ k, padCheck W L P (Y k) = true) (e : BivExpr) (hok : ok W S n L B e = true)
    (hlen : 0 < len L e) (hD : momentOk S D (len L e) = true)
    (hfit : 2 * (len L e * (bnd S L B e * D)) < 2 ^ W) :
    (D : ℝ) * ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        eval S L (fun k ↦ rowCoef W L (Y k)) e x y =
      (num W S L (fun k ↦ rowOfNat W L (Y k)) (momentRow W S D (len L e)) e : ℝ) := by
  have hW : 0 < W := by omega
  set cenv : ℕ → ℕ → ℤ := fun k ↦ rowCoef W L (Y k) with hcenv
  have hvars : ∀ k, BivSupp S n L (cenv k) := fun k ↦ bivSupp_rowCoef hP (hpad k)
  have hB : ∀ k q, |cenv k q| ≤ (B : ℤ) := fun k q ↦
    ((rowOfNat_eq hg (hguard k)).2 q).trans (by exact_mod_cast hgB)
  have henv : ∀ k, rowOfNat W L (Y k) = zPack W L (cenv k) := fun k ↦
    (rowOfNat_eq hg (hguard k)).1
  have hfun : ∀ x y, eval S L cenv e x y = bivEval S (coef S L cenv e) (len L e) x y :=
    eval_eq hS hvars e hok
  simp only [hfun]
  rw [integral_bivEval, num, pack_eq hS hW hvars hB henv e hok,
    momentNum_eq hW hlen (abs_coef_le hB e) hD hfit]

end BivExpr

/-! ### The test of one cell -/

/-- The mask of the slots of degree at least `n` in `x`, for rows of `L` slots with stride
`S`. -/
def padMask (W S n L : ℕ) : ℕ :=
  packSlots W L fun q ↦ cond (Nat.ble n (Nat.mod q S)) (slotMask W) 0

/-- The mask has a full slot wherever the degree in `x` is at least `n`. -/
theorem slot_padMask {W S n L q : ℕ} (hq : q < L) (hn : n ≤ q % S) :
    slot W q (padMask W S n L) = slotMask W := by
  have hlt : ∀ k < L, cond (Nat.ble n (Nat.mod k S)) (slotMask W) 0 < 2 ^ W := fun k _ ↦ by
    have h1 : slotMask W < 2 ^ W := by
      rw [slotMask_eq]
      exact Nat.sub_lt (Nat.two_pow_pos W) one_pos
    cases Nat.ble n (Nat.mod k S)
    · exact Nat.two_pow_pos W
    · exact h1
  have hble : Nat.ble n (Nat.mod q S) = true := Nat.ble_eq.mpr hn
  rw [padMask, slot_packed_eq hlt, ite_eq_left hq, hble, Bool.cond_true]

/-- The stored row of the variable `v`: `rows v` for `v < vars`, and `rows 0` otherwise, so a
variable of an expression with an index from `vars` on reads row `0`. -/
def rowAt (rows : ℕ → ℕ) (vars v : ℕ) : ℕ := cond (Nat.blt v vars) (rows v) (rows 0)

namespace BivExpr

/-- The test of the sizes, once for all cells: a positive stride, the guard width `g` below the
slot width `W`, the guard bound `slotBias g` at most the coefficient bound `B`, the test of the
expression, a row of positive length, a common multiple `D` of the denominators, the fit of the
last product, and `D` positive (with `D = 0` every bound for `D` times an integral would hold and
say nothing). -/
def sizesOk (W S n L g B D : ℕ) (e : BivExpr) : Bool :=
  Nat.blt 0 S && Nat.blt g W && Nat.ble (slotBias g) B && ok W S n L B e &&
    Nat.blt 0 (len L e) && momentOk S D (len L e) &&
    Nat.blt (Nat.mul 2 (Nat.mul (len L e) (Nat.mul (bnd S L B e) D))) (Nat.shiftLeft 1 W) &&
    Nat.blt 0 D

/-- The test of one cell for the residual `R`: the guards of its `vars` stored rows, and
`num (R * R) ≤ bound`. -/
def sqCheck (W S n L g D vars : ℕ) (rows : ℕ → ℕ) (R : BivExpr) (bound : ℕ) : Bool :=
  natAll vars (fun v ↦ signedGuardCheck W g L (rows v) &&
    padCheck W L (padMask W S n L) (rows v)) &&
  Nat.ble (Int.toNat (num W S L (fun v ↦ rowOfNat W L (rowAt rows vars v))
    (momentRow W S D (len L (mul R R))) (mul R R))) bound

/-- **The squared residual of one cell.** If the sizes pass `sizesOk` for `R * R` and the cell
passes `sqCheck` with `vars > 0`, then `D` times the integral over the unit square of the square
of the real function of `R` is at most `bound`. The real function is built from the polynomials
of the stored rows by the operations of `R`, with `dx` and `dy` the partial derivatives. -/
theorem sq_integral_le {W S n L g B D vars bound : ℕ} {rows : ℕ → ℕ} {R : BivExpr}
    (hsizes : sizesOk W S n L g B D (mul R R) = true) (hvars : 0 < vars)
    (hcell : sqCheck W S n L g D vars rows R bound = true) :
    (D : ℝ) * ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        eval S L (fun v ↦ rowCoef W L (rowAt rows vars v)) R x y ^ 2 ≤ bound := by
  simp only [sizesOk, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hsizes
  obtain ⟨⟨⟨⟨⟨⟨⟨hS, hg⟩, hgB⟩, hok⟩, hlen⟩, hD⟩, hfit⟩, -⟩ := hsizes
  simp only [sqCheck, Bool.and_eq_true] at hcell
  obtain ⟨hrows, hnum⟩ := hcell
  have hall : ∀ v, signedGuardCheck W g L (rowAt rows vars v) = true ∧
      padCheck W L (padMask W S n L) (rowAt rows vars v) = true := by
    intro v
    unfold rowAt
    cases hv : Nat.blt v vars with
    | true =>
      simpa only [Bool.cond_true, Bool.and_eq_true] using natAll_spec hrows (Nat.blt_eq.mp hv)
    | false => simpa only [Bool.cond_false, Bool.and_eq_true] using natAll_spec hrows hvars
  have hfit' : 2 * (len L (mul R R) * (bnd S L B (mul R R) * D)) < 2 ^ W := by
    change 2 * (len L (mul R R) * (bnd S L B (mul R R) * D)) < 1 <<< W at hfit
    rwa [Nat.one_shiftLeft] at hfit
  have hint := integral_eq (P := padMask W S n L) (Y := rowAt rows vars) hS hg hgB
    (fun k ↦ (hall k).1) (fun q hq hn ↦ slot_padMask hq hn) (fun k ↦ (hall k).2) (mul R R) hok
    hlen hD hfit'
  have hsq : ∀ x y, eval S L (fun v ↦ rowCoef W L (rowAt rows vars v)) R x y ^ 2 =
      eval S L (fun v ↦ rowCoef W L (rowAt rows vars v)) (mul R R) x y := fun x y ↦ by
    change _ = eval S L _ R x y * eval S L _ R x y
    ring
  simp only [hsq]
  rw [hint]
  have hle : num W S L (fun v ↦ rowOfNat W L (rowAt rows vars v))
      (momentRow W S D (len L (mul R R))) (mul R R) ≤ (bound : ℤ) :=
    (Int.self_le_toNat _).trans (by exact_mod_cast Nat.ble_eq.mp hnum)
  exact_mod_cast hle

/-- **The squared residual of one cell, as a bound for the integral.** Under the tests of
`sq_integral_le`, the integral over the unit square of the square of the real function of `R`
is at most `bound / D`, with `D > 0` from `sizesOk`. -/
theorem sq_integral_le_div {W S n L g B D vars bound : ℕ} {rows : ℕ → ℕ} {R : BivExpr}
    (hsizes : sizesOk W S n L g B D (mul R R) = true) (hvars : 0 < vars)
    (hcell : sqCheck W S n L g D vars rows R bound = true) :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        eval S L (fun v ↦ rowCoef W L (rowAt rows vars v)) R x y ^ 2 ≤ (bound : ℝ) / D := by
  have hD : (0 : ℝ) < D := by
    have h := hsizes
    simp only [sizesOk, Bool.and_eq_true, Nat.blt_eq] at h
    exact_mod_cast h.2
  rw [le_div_iff₀ hD, mul_comm]
  exact sq_integral_le hsizes hvars hcell

end BivExpr

end CAS.Numerics

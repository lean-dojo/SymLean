/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset

/-!
# Rounding errors of a conversion followed by an evaluation

Values `x l` known as integers `X l` within `1` of `2 ^ a x l` (with `|X l| ≤ Bx`), conversion
coefficients `c l j` with `|c l j| ≤ Bc` known within `1 / 2` of `2 ^ b c l j`, the converted
integers `Y j = ⌊∑ l X l C l j / 2 ^ b⌋` and exact mode values `t j` with `|t j| ≤ Bt`: the
integer evaluation `∑ j Y j (2 ^ a t j) / 2 ^ (a + a)` is within
`q Bt (2 ^ (-a) + n ((Bc + 1) / 2 ^ a + (Bx + 1) / 2 ^ a / 2 ^ (b + 1)))` of
`∑ j (∑ l x l c l j) t j` (`conversion_evaluation_error_le`, for all exponents `a` and `b`, all
bounds and all sizes `n` and `q`). Without the conversion, `∑ l X l (2 ^ a t l) / 2 ^ (a + a)` is
within `n Bt / 2 ^ a` of `∑ l x l t l` (`evaluation_error_le`).

`abs_conversion_evaluation_sub_le` follows from the instance with the scales `2 ^ 48` and
`2 ^ 80` and the bounds `2 ^ 61`, `2 ^ 10` and `2`: its bound has the larger `2 ^ 13 + 1` in the
place of `(2 ^ 61 + 1) / 2 ^ 48`. `abs_evaluation_sub_le` is the instance with the scale `2 ^ 48`
and the bound `2`.

## Implementation notes

We bound each product and add the bounds. From `|X l| ≤ Bx` we get `|x l| ≤ (Bx + 1) / 2 ^ a`, and
the split `X C / 2 ^ (a + b) - x c = (X / 2 ^ a - x) (C / 2 ^ b) + x (C / 2 ^ b - c)` bounds one
product by `(Bc + 1) / 2 ^ a + (Bx + 1) / 2 ^ a / 2 ^ (b + 1)`. The floor in `Y j` adds `2 ^ (-a)`
after scaling, and `|t j| ≤ Bt` gives the factor `Bt`. Only the distances of `X` and `C` from the
scaled values enter, so they may come from any rounding within those distances.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-- **Rounding error of a conversion followed by an evaluation.** For `l : Fin n` and `j : Fin q`,
let `X l` be integers with `|X l - 2 ^ a * x l| ≤ 1` and `|X l| ≤ Bx`, `C l j` integers with
`|C l j - 2 ^ b * c l j| ≤ 1 / 2` and `|c l j| ≤ Bc`, `Y j` the floor of
`(∑ l, X l * C l j) / 2 ^ b`, and `|t j| ≤ Bt`. Then `(∑ j, Y j * (2 ^ a * t j)) / 2 ^ (a + a)`
lies within `q * Bt * (1 / 2 ^ a + n * ((Bc + 1) / 2 ^ a + (Bx + 1) / 2 ^ a / 2 ^ (b + 1)))` of
`∑ j, (∑ l, x l * c l j) * t j`. This holds for all exponents `a` and `b`, all real bounds `Bx`,
`Bc` and `Bt`, and all sizes `n` and `q`. -/
theorem conversion_evaluation_error_le {n q a b : ℕ} {Bx Bc Bt : ℝ} (x : Fin n → ℝ)
    (X : Fin n → ℤ) (c : Fin n → Fin q → ℝ) (C : Fin n → Fin q → ℤ) (Y : Fin q → ℤ)
    (t : Fin q → ℝ)
    (hX : ∀ l, |(X l : ℝ) - 2 ^ a * x l| ≤ 1) (hXb : ∀ l, |(X l : ℝ)| ≤ Bx)
    (hC : ∀ l j, |(C l j : ℝ) - 2 ^ b * c l j| ≤ 1 / 2) (hc : ∀ l j, |c l j| ≤ Bc)
    (hY : ∀ j, (Y j : ℝ) ≤ (∑ l, (X l : ℝ) * C l j) / 2 ^ b ∧
      (∑ l, (X l : ℝ) * C l j) / 2 ^ b < Y j + 1)
    (ht : ∀ j, |t j| ≤ Bt) :
    |(∑ j, (Y j : ℝ) * (2 ^ a * t j)) / 2 ^ (a + a) - ∑ j, (∑ l, x l * c l j) * t j| ≤
      (q : ℝ) * Bt *
        (1 / 2 ^ a + (n : ℝ) * ((Bc + 1) / 2 ^ a + (Bx + 1) / 2 ^ a / 2 ^ (b + 1))) := by
  have h2a : (0 : ℝ) < 2 ^ a := by positivity
  have h2b : (0 : ℝ) < 2 ^ b := by positivity
  have hterm : ∀ l j, |(X l : ℝ) * C l j / 2 ^ (a + b) - x l * c l j| ≤
      (Bc + 1) / 2 ^ a + (Bx + 1) / 2 ^ a / 2 ^ (b + 1) := by
    intro l j
    have ha : |(X l : ℝ) / 2 ^ a - x l| ≤ 1 / 2 ^ a := by
      rw [show (X l : ℝ) / 2 ^ a - x l = ((X l : ℝ) - 2 ^ a * x l) / 2 ^ a by field_simp,
        abs_div, abs_of_pos h2a]
      exact div_le_div_of_nonneg_right (hX l) h2a.le
    have hd : |(C l j : ℝ) / 2 ^ b - c l j| ≤ 1 / 2 ^ (b + 1) := by
      rw [show (C l j : ℝ) / 2 ^ b - c l j = ((C l j : ℝ) - 2 ^ b * c l j) / 2 ^ b by field_simp,
        abs_div, abs_of_pos h2b, pow_succ, ← div_div, div_right_comm]
      exact div_le_div_of_nonneg_right (hC l j) h2b.le
    have hone : (1 : ℝ) / 2 ^ (b + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
    have hb : |(C l j : ℝ) / 2 ^ b| ≤ Bc + 1 := by
      have h := abs_add_le ((C l j : ℝ) / 2 ^ b - c l j) (c l j)
      rw [sub_add_cancel] at h
      linarith [hc l j]
    have hx : |x l| ≤ (Bx + 1) / 2 ^ a := by
      have h := abs_sub (x l - (X l : ℝ) / 2 ^ a) (-((X l : ℝ) / 2 ^ a))
      rw [sub_neg_eq_add, sub_add_cancel, abs_neg, abs_sub_comm, abs_div, abs_of_pos h2a] at h
      have hXd : |(X l : ℝ)| / 2 ^ a ≤ Bx / 2 ^ a := div_le_div_of_nonneg_right (hXb l) h2a.le
      rw [add_div]
      linarith
    rw [show (X l : ℝ) * C l j / 2 ^ (a + b) - x l * c l j =
        ((X l : ℝ) / 2 ^ a - x l) * (C l j / 2 ^ b) + x l * (C l j / 2 ^ b - c l j) by
      rw [pow_add]
      field_simp
      ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 := mul_le_mul ha hb (abs_nonneg _) (by positivity)
    have h2 := mul_le_mul hx hd (abs_nonneg _) ((abs_nonneg _).trans hx)
    rw [show (Bc + 1) / 2 ^ a = 1 / 2 ^ a * (Bc + 1) by ring,
      show (Bx + 1) / 2 ^ a / 2 ^ (b + 1) = (Bx + 1) / 2 ^ a * (1 / 2 ^ (b + 1)) by ring]
    exact add_le_add h1 h2
  have hE : ∀ j, |(Y j : ℝ) / 2 ^ a - ∑ l, x l * c l j| ≤
      1 / 2 ^ a + (n : ℝ) * ((Bc + 1) / 2 ^ a + (Bx + 1) / 2 ^ a / 2 ^ (b + 1)) := by
    intro j
    have hS : |(∑ l, (X l : ℝ) * C l j) / 2 ^ (a + b) - ∑ l, x l * c l j| ≤
        (n : ℝ) * ((Bc + 1) / 2 ^ a + (Bx + 1) / 2 ^ a / 2 ^ (b + 1)) := by
      rw [sum_div, ← sum_sub_distrib]
      refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun l _ ↦ hterm l j).trans ?_)
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    obtain ⟨hS₁, hS₂⟩ := abs_le.mp hS
    obtain ⟨hY₁, hY₂⟩ := hY j
    have hdiv : (∑ l, (X l : ℝ) * C l j) / 2 ^ (a + b) =
        (∑ l, (X l : ℝ) * C l j) / 2 ^ b / 2 ^ a := by
      rw [pow_add, div_div, mul_comm]
    have hY₁' : (Y j : ℝ) / 2 ^ a ≤ (∑ l, (X l : ℝ) * C l j) / 2 ^ (a + b) := by
      rw [hdiv]
      exact div_le_div_of_nonneg_right hY₁ h2a.le
    have hY₂' : (∑ l, (X l : ℝ) * C l j) / 2 ^ (a + b) < (Y j : ℝ) / 2 ^ a + 1 / 2 ^ a := by
      rw [hdiv, ← add_div]
      exact div_lt_div_of_pos_right hY₂ h2a
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hsplit : (∑ j, (Y j : ℝ) * (2 ^ a * t j)) / 2 ^ (a + a) - ∑ j, (∑ l, x l * c l j) * t j =
      ∑ j, ((Y j : ℝ) / 2 ^ a - ∑ l, x l * c l j) * t j := by
    rw [sum_div, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [pow_add]
    field_simp
  rw [hsplit]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j, |((Y j : ℝ) / 2 ^ a - ∑ l, x l * c l j) * t j| ≤
        ∑ _j : Fin q,
          (1 / 2 ^ a + (n : ℝ) * ((Bc + 1) / 2 ^ a + (Bx + 1) / 2 ^ a / 2 ^ (b + 1))) * Bt :=
        sum_le_sum fun j _ ↦ by
          rw [abs_mul]
          exact mul_le_mul (hE j) (ht j) (abs_nonneg _) ((abs_nonneg _).trans (hE j))
    _ = _ := by
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- A consequence of `conversion_evaluation_error_le` at the scales `2 ^ 48` and `2 ^ 80` and the
bounds `2 ^ 61`, `2 ^ 10` and `2`, with the larger `2 ^ 13 + 1` in the place of
`(2 ^ 61 + 1) / 2 ^ 48`: for integers `X l` with `|X l - 2 ^ 48 * x l| ≤ 1` and
`|X l| ≤ 2 ^ 61`, integers `C l j` with `|C l j - 2 ^ 80 * c l j| ≤ 1 / 2` and `|c l j| ≤ 2 ^ 10`,
`Y j` the floor of `(∑ l, X l * C l j) / 2 ^ 80`, and `|t j| ≤ 2`, the value
`(∑ j, Y j * (2 ^ 48 * t j)) / 2 ^ 96` lies within
`q * 2 * (1 / 2 ^ 48 + n * ((2 ^ 10 + 1) / 2 ^ 48 + (2 ^ 13 + 1) / 2 ^ 81))` of
`∑ j, (∑ l, x l * c l j) * t j`. -/
theorem abs_conversion_evaluation_sub_le {n q : ℕ} (x : Fin n → ℝ) (X : Fin n → ℤ)
    (c : Fin n → Fin q → ℝ) (C : Fin n → Fin q → ℤ) (Y : Fin q → ℤ) (t : Fin q → ℝ)
    (hX : ∀ l, |(X l : ℝ) - 2 ^ 48 * x l| ≤ 1) (hXb : ∀ l, |(X l : ℝ)| ≤ 2 ^ 61)
    (hC : ∀ l j, |(C l j : ℝ) - 2 ^ 80 * c l j| ≤ 1 / 2) (hc : ∀ l j, |c l j| ≤ 2 ^ 10)
    (hY : ∀ j, (Y j : ℝ) ≤ (∑ l, (X l : ℝ) * C l j) / 2 ^ 80 ∧
      (∑ l, (X l : ℝ) * C l j) / 2 ^ 80 < Y j + 1)
    (ht : ∀ j, |t j| ≤ 2) :
    |(∑ j, (Y j : ℝ) * (2 ^ 48 * t j)) / 2 ^ 96 - ∑ j, (∑ l, x l * c l j) * t j| ≤
      (q : ℝ) * 2 * (1 / 2 ^ 48 + (n : ℝ) * ((2 ^ 10 + 1) / 2 ^ 48 + (2 ^ 13 + 1) / 2 ^ 81)) :=
  (conversion_evaluation_error_le (a := 48) (b := 80) x X c C Y t hX hXb hC hc hY ht).trans <| by
    gcongr
    norm_num

/-- **Rounding error of an evaluation.** For integers `X l` with `|X l - 2 ^ a * x l| ≤ 1` and
reals `t l` with `|t l| ≤ Bt`, the value `(∑ l, X l * (2 ^ a * t l)) / 2 ^ (a + a)` lies within
`n * Bt / 2 ^ a` of `∑ l, x l * t l`, for every exponent `a`, every real bound `Bt` and every
size `n`. -/
theorem evaluation_error_le {n a : ℕ} {Bt : ℝ} (x : Fin n → ℝ) (X : Fin n → ℤ) (t : Fin n → ℝ)
    (hX : ∀ l, |(X l : ℝ) - 2 ^ a * x l| ≤ 1) (ht : ∀ l, |t l| ≤ Bt) :
    |(∑ l, (X l : ℝ) * (2 ^ a * t l)) / 2 ^ (a + a) - ∑ l, x l * t l| ≤ (n : ℝ) * Bt / 2 ^ a := by
  have h2 : (0 : ℝ) < 2 ^ a := by positivity
  have hsplit : (∑ l, (X l : ℝ) * (2 ^ a * t l)) / 2 ^ (a + a) - ∑ l, x l * t l =
      ∑ l, ((X l : ℝ) - 2 ^ a * x l) / 2 ^ a * t l := by
    rw [sum_div, ← sum_sub_distrib]
    refine sum_congr rfl fun l _ ↦ ?_
    rw [pow_add]
    field_simp
  rw [hsplit]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ l, |((X l : ℝ) - 2 ^ a * x l) / 2 ^ a * t l| ≤ ∑ _l : Fin n, 1 / 2 ^ a * Bt :=
        sum_le_sum fun l _ ↦ by
          rw [abs_mul, abs_div, abs_of_pos h2]
          exact mul_le_mul (div_le_div_of_nonneg_right (hX l) h2.le) (ht l)
            (abs_nonneg _) (by positivity)
    _ = _ := by
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The instance of `evaluation_error_le` with the scale `2 ^ 48` and the bound `2`: for integers
`X l` with `|X l - 2 ^ 48 * x l| ≤ 1` and reals `t l` with `|t l| ≤ 2`, the value
`(∑ l, X l * (2 ^ 48 * t l)) / 2 ^ 96` lies within `n * 2 / 2 ^ 48` of `∑ l, x l * t l`. -/
theorem abs_evaluation_sub_le {n : ℕ} (x : Fin n → ℝ) (X : Fin n → ℤ) (t : Fin n → ℝ)
    (hX : ∀ l, |(X l : ℝ) - 2 ^ 48 * x l| ≤ 1) (ht : ∀ l, |t l| ≤ 2) :
    |(∑ l, (X l : ℝ) * (2 ^ 48 * t l)) / 2 ^ 96 - ∑ l, x l * t l| ≤ (n : ℝ) * 2 / 2 ^ 48 :=
  evaluation_error_le (a := 48) x X t hX ht

end CAS.Numerics

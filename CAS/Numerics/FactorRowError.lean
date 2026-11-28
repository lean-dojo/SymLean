/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.SeparableRows
public import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

/-!
# The error of one three-stage factor row

A value given as the separable triple sum of data slots over `2^s₁`, first-stage coefficients
`R m - α₁` over `2^s₂`, conversion slots over `2^e`, integer factors and node slots over `2^s₃`
is within `Σ_k |c_k| |G_k n| / 2^(s₁ + s₂ + s₃)` of slot `n` of `factorRow` over
`2^(s₁ + s₂ + s₃)`, when the rows fit their slots, the shift `e` is below the width `w₂` and the
three stages fit their slots; the fits of the stages follow from bounds on the entries.
`abs_sub_factorRow_le` proves this for every number of data slots, every number and width of
node slots, all bounds on the entries and all exponents `s₁`, `s₂` and `s₃`. The error comes
from the floor in the second stage. `abs_sub_signedSlot_factorRow_le` is its instance with `150`
data slots, `613` node slots of width `352` bounded by `2^63`, and the scales `2^120`, `2^62` and
`2^62`. `natAbs_sum_mul_le` bounds the absolute value of a sum of `n` products by `n a b`.

## Implementation notes

We follow the value through the stages of `factorRow`. The first two stages are exact under the
width conditions `h₁` and `h₂` (`signedSlot_factorRow_stages`). The shift replaces `Y k / 2^e` by
its floor `z k` (`slotShift_floor`), the only rounding. A shifted slot is bounded by
`2^(w₂ - 1 - e)` from its width alone, so `h₃` makes the third stage fit and `hα` keeps every
biased coefficient nonnegative, and `signedSlot_factorRow` reads the final slot exactly. The error
of slot `n` is then `∑ k c_k (Y k / 2^e - z k) G_k n / 2^(s₁ + s₂ + s₃)`, which gives the bound
since `|Y k / 2^e - z k| ≤ 1`.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-- A sum of `n` products `x j * y j` with `|x j| ≤ a` and `|y j| ≤ b` is at most `n * a * b`
in absolute value. -/
theorem natAbs_sum_mul_le {n a b : ℕ} {x y : ℕ → ℤ} (hx : ∀ j < n, (x j).natAbs ≤ a)
    (hy : ∀ j < n, (y j).natAbs ≤ b) : (∑ j ∈ range n, x j * y j).natAbs ≤ n * a * b := by
  refine (Int.natAbs_sum_le _ _).trans
    ((sum_le_card_nsmul _ _ (a * b) fun j hj ↦ ?_).trans_eq (by simp [mul_assoc]))
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul (hx j (mem_range.mp hj)) (hy j (mem_range.mp hj))

/-- **Error of one three-stage factor row.** If a value is the separable triple sum of the data
slots over `2^s₁`, the first-stage coefficients `R m - α₁` over `2^s₂`, the conversion slots
over `2^e`, the integer factors `c_k = cp k - cn k` and the node slots over `2^s₃`, then slot `n`
of the factor row over `2^(s₁ + s₂ + s₃)` is within `Σ_k |c_k| |G_k n| / 2^(s₁ + s₂ + s₃)` of
it. This holds for every number `q₁` of data slots, every number `q₃` of node slots of every
width `w₃`, every slot `n < q₃` and all exponents `s₁`, `s₂` and `s₃`. The rows `D m`, `K l` and
`G k` fit their slots, and `e < w₂`. The data slots, the coefficients `R m - α₁`, the conversion
slots, the factors and the node slots are at most `Db`, `Rb`, `Kb`, `cb` and `Gb` in absolute
value. The hypotheses `h₁`, `h₂`, `h₃` and `hα` on these bounds make the three stages fit their
slots, and the error comes from the floor in the second stage. -/
theorem abs_sub_factorRow_le {w₁ q₁ M' α₁ w₂ q₂ e w₃ q₃ α₃ : ℕ} {R D K cp cn G : ℕ → ℕ}
    {Db Rb Kb cb Gb s₁ s₂ s₃ : ℕ} (approx : ℝ) {n : ℕ} (hn : n < q₃)
    (happrox : approx = ∑ m ∈ range M', ∑ l ∈ range q₁,
      (signedSlot w₁ l (D m) : ℝ) / 2 ^ s₁ * ((((R m : ℤ) - α₁ : ℤ) : ℝ) / 2 ^ s₂) *
        ∑ k ∈ range q₂, (signedSlot w₂ k (K l) : ℝ) / 2 ^ e *
          (((cp k : ℤ) - cn k : ℤ) : ℝ) * ((signedSlot w₃ n (G k) : ℝ) / 2 ^ s₃))
    (hDrow : ∀ m < M', D m < 2 ^ (w₁ * q₁)) (hKrow : ∀ l < q₁, K l < 2 ^ (w₂ * q₂))
    (hGrow : ∀ k < q₂, G k < 2 ^ (w₃ * q₃))
    (hD : ∀ m < M', ∀ l < q₁, (signedSlot w₁ l (D m)).natAbs ≤ Db)
    (hR : ∀ m < M', ((R m : ℤ) - α₁).natAbs ≤ Rb)
    (hK : ∀ l < q₁, ∀ k < q₂, (signedSlot w₂ k (K l)).natAbs ≤ Kb)
    (hc : ∀ k < q₂, ((cp k : ℤ) - cn k).natAbs ≤ cb)
    (hG : ∀ n < q₃, ∀ k < q₂, (signedSlot w₃ n (G k)).natAbs ≤ Gb)
    (he : e < w₂) (h₁ : 2 * M' * Rb * Db < 2 ^ w₁) (h₂ : 2 * q₁ * (M' * Rb * Db) * Kb < 2 ^ w₂)
    (h₃ : 2 * q₂ * (cb * 2 ^ (w₂ - 1 - e)) * Gb < 2 ^ w₃)
    (hα : cb * 2 ^ (w₂ - 1 - e) ≤ α₃) :
    |approx - (signedSlot w₃ n (factorRow w₁ q₁ M' α₁ R D w₂ q₂ K e w₃ q₃ α₃ cp cn G) : ℝ) /
        2 ^ (s₁ + s₂ + s₃)| ≤
      ∑ k ∈ range q₂,
        |(((cp k : ℤ) - cn k : ℤ) : ℝ)| * |(signedSlot w₃ n (G k) : ℝ)| / 2 ^ (s₁ + s₂ + s₃) := by
  -- stage 1
  set H : ℕ → ℤ := fun l ↦ ∑ m ∈ range M', ((R m : ℤ) - α₁) * signedSlot w₁ l (D m)
  have hH : ∀ l < q₁, (H l).natAbs ≤ M' * Rb * Db := fun l hl ↦
    natAbs_sum_mul_le (fun m hm ↦ hR m hm) (fun m hm ↦ hD m hm l hl)
  have hfit₁ : ∀ l < q₁, FitsSlot w₁ (H l) := fun l hl ↦
    fitsSlot_sum_mul (fun m hm ↦ hR m hm) (fun m hm ↦ hD m hm l hl) h₁
  -- stage 2
  set Y : ℕ → ℤ := fun k ↦ ∑ l ∈ range q₁, H l * signedSlot w₂ k (K l)
  have hfit₂ : ∀ k < q₂, FitsSlot w₂ (Y k) := fun k hk ↦
    fitsSlot_sum_mul (fun l hl ↦ hH l hl) (fun l hl ↦ hK l hl k hk) h₂
  set row₂ := packedRowCombination w₂ q₂ q₁ (slotBias w₁)
    (fun l ↦ slot w₁ l (packedRowCombination w₁ q₁ M' α₁ R D)) K
  have hY : ∀ k < q₂, signedSlot w₂ k row₂ = Y k := fun k hk ↦
    signedSlot_factorRow_stages hDrow hKrow hfit₁ hfit₂ hk
  -- the shifted second stage
  set z : ℕ → ℤ := fun k ↦ (slotShift w₂ e k row₂ : ℤ) - 2 ^ (w₂ - 1 - e)
  have hzf : ∀ k < q₂, ((z k : ℤ) : ℝ) ≤ (Y k : ℝ) / 2 ^ e ∧ (Y k : ℝ) / 2 ^ e < (z k : ℝ) + 1 := by
    intro k hk
    have h := slotShift_floor he k row₂
    rw [hY k hk] at h
    push_cast [z] at h ⊢
    exact h
  have hz : ∀ k < q₂, (z k).natAbs ≤ 2 ^ (w₂ - 1 - e) := by
    intro k hk
    have hlt : slotShift w₂ e k row₂ < 2 * 2 ^ (w₂ - 1 - e) := by
      rw [← pow_succ', show w₂ - 1 - e + 1 = w₂ - e by omega]
      change slot w₂ k row₂ >>> e < _
      rw [Nat.shiftRight_eq_div_pow]
      refine Nat.div_lt_of_lt_mul ?_
      rw [← pow_add, Nat.add_sub_cancel' he.le]
      exact slot_lt _ _ _
    simp only [z]
    rw [show (2 : ℤ) ^ (w₂ - 1 - e) = ((2 ^ (w₂ - 1 - e) : ℕ) : ℤ) by push_cast; rfl]
    generalize 2 ^ (w₂ - 1 - e) = P at hlt ⊢
    omega
  have hcz : ∀ k < q₂, (((cp k : ℤ) - cn k) * z k).natAbs ≤ cb * 2 ^ (w₂ - 1 - e) := by
    intro k hk
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (hc k hk) (hz k hk)
  -- stage 3
  have hα' : ∀ k < q₂, ((cp k : ℤ) - cn k) * ((slotShift w₂ e k row₂ : ℤ) - 2 ^ (w₂ - 1 - e)) +
      α₃ ≥ 0 := fun k hk ↦ by
    have h := hcz k hk
    simp only [z] at h
    omega
  have hfit₃ : ∀ n < q₃, FitsSlot w₃ (∑ k ∈ range q₂, ((cp k : ℤ) - cn k) *
      ((slotShift w₂ e k row₂ : ℤ) - 2 ^ (w₂ - 1 - e)) * signedSlot w₃ n (G k)) :=
    fun n hn ↦ fitsSlot_sum_mul (fun k hk ↦ hcz k hk) (fun k hk ↦ hG n hn k hk) h₃
  rw [signedSlot_factorRow hGrow hα' hfit₃ hn]
  set c : ℕ → ℝ := fun k ↦ (((cp k : ℤ) - cn k : ℤ) : ℝ)
  set g : ℕ → ℝ := fun k ↦ (signedSlot w₃ n (G k) : ℝ)
  have happrox' : approx =
      ∑ k ∈ range q₂, c k * g k * ((Y k : ℝ) / 2 ^ e) / 2 ^ (s₁ + s₂ + s₃) := by
    rw [happrox]
    simp only [Y, H, c, g]
    push_cast
    simp only [mul_sum, sum_mul, sum_div]
    rw [show (∑ m ∈ range M', ∑ l ∈ range q₁, ∑ k ∈ range q₂, _) =
      ∑ k ∈ range q₂, ∑ l ∈ range q₁, ∑ m ∈ range M', _ from by
        rw [sum_congr rfl fun m _ ↦ sum_comm, sum_comm]
        exact sum_congr rfl fun k _ ↦ sum_comm]
    refine sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ sum_congr rfl fun m _ ↦ ?_
    rw [show (2 : ℝ) ^ (s₁ + s₂ + s₃) = 2 ^ s₁ * 2 ^ s₂ * 2 ^ s₃ by rw [pow_add, pow_add]]
    field_simp
  rw [happrox', ← sum_div]
  push_cast
  rw [← sub_div, ← sum_sub_distrib, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (s₁ + s₂ + s₃)), ← sum_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk ↦ ?_)
  have hk' := mem_range.mp hk
  obtain ⟨h1, h2⟩ := hzf k hk'
  have hd : |(Y k : ℝ) / 2 ^ e - (z k : ℝ)| ≤ 1 :=
    abs_le.mpr ⟨by linarith only [h1], by linarith only [h2]⟩
  calc |c k * g k * ((Y k : ℝ) / 2 ^ e) -
        ((cp k : ℝ) - cn k) * (((slotShift w₂ e k row₂ : ℕ) : ℝ) - 2 ^ (w₂ - 1 - e)) * g k|
      = |c k| * |g k| * |(Y k : ℝ) / 2 ^ e - (z k : ℝ)| := by
        rw [← abs_mul, ← abs_mul]
        congr 1
        simp only [c, z]
        push_cast
        ring
    _ ≤ |c k| * |g k| * 1 := by gcongr
    _ = |((cp k : ℝ) - cn k)| * |(signedSlot w₃ n (G k) : ℝ)| := by
        simp only [c, g, mul_one]
        push_cast
        rfl

/-- The instance of `abs_sub_factorRow_le` with 150 data slots, 613 node slots of 352 bits that
are at most `2^63` in absolute value, and the scales `2^120`, `2^62` and `2^62`: slot `n < 613`
of the factor row over `2^244` is within `Σ_k |c_k| |G_k n| / 2^244` of the value. -/
theorem abs_sub_signedSlot_factorRow_le {w₁ M' α₁ w₂ q₂ e α₃ : ℕ} {R D K cp cn G : ℕ → ℕ}
    {Db Rb Kb cb : ℕ} (approx : ℝ) {n : ℕ} (hn : n < 613)
    (happrox : approx = ∑ m ∈ range M', ∑ l ∈ range 150,
      (signedSlot w₁ l (D m) : ℝ) / 2 ^ 120 * ((((R m : ℤ) - α₁ : ℤ) : ℝ) / 2 ^ 62) *
        ∑ k ∈ range q₂, (signedSlot w₂ k (K l) : ℝ) / 2 ^ e *
          (((cp k : ℤ) - cn k : ℤ) : ℝ) * ((signedSlot 352 n (G k) : ℝ) / 2 ^ 62))
    (hDrow : ∀ m < M', D m < 2 ^ (w₁ * 150)) (hKrow : ∀ l < 150, K l < 2 ^ (w₂ * q₂))
    (hGrow : ∀ k < q₂, G k < 2 ^ (352 * 613))
    (hD : ∀ m < M', ∀ l < 150, (signedSlot w₁ l (D m)).natAbs ≤ Db)
    (hR : ∀ m < M', ((R m : ℤ) - α₁).natAbs ≤ Rb)
    (hK : ∀ l < 150, ∀ k < q₂, (signedSlot w₂ k (K l)).natAbs ≤ Kb)
    (hc : ∀ k < q₂, ((cp k : ℤ) - cn k).natAbs ≤ cb)
    (hG : ∀ n < 613, ∀ k < q₂, (signedSlot 352 n (G k)).natAbs ≤ 2 ^ 63)
    (he : e < w₂) (h₁ : 2 * M' * Rb * Db < 2 ^ w₁) (h₂ : 2 * 150 * (M' * Rb * Db) * Kb < 2 ^ w₂)
    (h₃ : 2 * q₂ * (cb * 2 ^ (w₂ - 1 - e)) * 2 ^ 63 < 2 ^ 352)
    (hα : cb * 2 ^ (w₂ - 1 - e) ≤ α₃) :
    |approx - (signedSlot 352 n (factorRow w₁ 150 M' α₁ R D w₂ q₂ K e 352 613 α₃ cp cn G) : ℝ) /
        2 ^ 244| ≤
      ∑ k ∈ range q₂,
        |(((cp k : ℤ) - cn k : ℤ) : ℝ)| * |(signedSlot 352 n (G k) : ℝ)| / 2 ^ 244 :=
  abs_sub_factorRow_le (s₁ := 120) (s₂ := 62) (s₃ := 62) approx hn happrox hDrow hKrow hGrow hD hR
    hK hc hG he h₁ h₂ h₃ hα

end CAS.Numerics

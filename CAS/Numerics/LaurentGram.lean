/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedSignedWindows
public import CAS.Numerics.PackedLaurent
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

/-!
# Gram values of rows of exponential coefficients by packed products

Rows of `q` integer coefficients `ξ_t` are stored with an offset, as packed natural numbers with
slots `c + ξ_t`. For an integer kernel `ν` with `ν 0 ≥ 0` and `ν r ≤ 0` for `r ≠ 0`, three packed
operations per row and one per pair give the bilinear form
`∑_{t,s} ξ_t η_s ν (q - 1 - t - s)` of two rows:

* `laurentWindow`: the window of slots `q - 1, …, 2q - 2` of the product with the packed row of
  `-ν`, one Toeplitz matrix applied to a row (`laurentWindow_eq`);
* `laurentApply`: the row `u_v + d` with `u_v = ∑_s ν (v - s) η_s`, from `ν 0` times the row, a
  constant row and the window (`laurentApply_eq`);
* `laurentGramValue`: the middle slot of the product of a row with an applied row, corrected by
  the two row sums (`laurentGramValue_eq`).

`packedRowCombination_eq_biasedPack`, `biasedPack_sub_offset` and `biasedPack_add_sub_offset`
bring biased rows, such as the output of a packed row combination, down to the offset `c`.

## Implementation notes

We store offsets `c + ξ_t` instead of signed entries so that every slot, product and window is
a natural number: the kernel evaluates natural-number literals with an arbitrary-precision
library (see [PackedSlots](PackedSlots.lean)) and has no such extension for `Int`. The sign
conditions on `ν` make the entries `-ν r`, `r ≠ 0`, natural, so they form a packed row, while
`ν 0` enters as a multiple of the row; the constant row in `laurentApply` keeps the applied row
nonnegative. The dot product is the middle slot of one product of packed rows, a Kronecker
substitution ([PackedConvolution](PackedConvolution.lean)), and the offsets come out through the
two row sums, each the middle slot of a product with the row of ones; only this final correction
in `laurentGramValue` uses a few integer operations on single numbers. The slot widths follow
from bounds on the slots.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-- When every row is below `2 ^ (w * q)` and every entry of the combination fits its slot, the
packed combination is the biased packing of its entries. -/
theorem packedRowCombination_eq_biasedPack {w q n α : ℕ} {s rows : ℕ → ℕ}
    (hrows : ∀ j < n, rows j < 2 ^ (w * q))
    (hfit : ∀ k < q,
      FitsSlot w (∑ j ∈ range n, ((s j : ℤ) - α) * signedSlot w k (rows j)))
 :
    packedRowCombination w q n α s rows =
      biasedPack w q (fun k ↦ ∑ j ∈ range n, ((s j : ℤ) - α) * signedSlot w k (rows j)) := by
  apply Nat.cast_injective (R := ℤ)
  rw [cast_packedRowCombination hrows hfit, biasedPack, packSlots_eq_sum]
  push_cast
  exact sum_congr rfl fun j hj ↦ by rw [encodeSlot_of_fits (hfit j (mem_range.mp hj))]

/-- Slots `q - 1, …, 2q - 2` of the product `N Y`. -/
def laurentWindow (W q N Y : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (Nat.mul N Y) (Nat.mul W (q - 1))) (slotMask (Nat.mul W q))

/-- The applied row `c0 * Y + C - laurentWindow W q N Y`, in natural numbers: `c0` is `ν 0`, `N`
the packed row of `-ν` and `C` a row of constants. -/
def laurentApply (W q c0 N C Y : ℕ) : ℕ :=
  Nat.sub (Nat.add (Nat.mul c0 Y) C) (laurentWindow W q N Y)

/-- The middle slot of the product of two rows of `q` slots. -/
def laurentPairSlot (W q X U : ℕ) : ℕ := slot W (q - 1) (Nat.mul X U)

/-- The sum of the slots of a row, as the middle slot of its product with the row of ones. -/
def laurentRowSum (W q X : ℕ) : ℕ := laurentPairSlot W q X (constSlots W q 1)

/-- The Gram value from the middle slot and the two row sums. -/
def laurentGramValue (W q c d X U : ℕ) : ℤ :=
  (laurentPairSlot W q X U : ℤ) - d * laurentRowSum W q X - c * laurentRowSum W q U + q * c * d

/-- If the slots of `n` are at most `a`, those of `y` at most `b` and `(2q - 1) a b < 2 ^ W`, the
window of the product of the packed rows is the packed row of the Toeplitz sums
`∑_u n_{v+q-1-u} y_u`, `v < q`. -/
theorem laurentWindow_eq {W q a b : ℕ} {n y : ℕ → ℕ}
    (hn : ∀ s < 2 * q - 1, n s ≤ a) (hy : ∀ u < q, y u ≤ b) (hW : (2 * q - 1) * a * b < 2 ^ W) :
    laurentWindow W q (packSlots W (2 * q - 1) n) (packSlots W q y) =
      packSlots W q (fun v ↦ ∑ u ∈ range q, n (v + (q - 1) - u) * y u) := by
  set P := packSlots W (2 * q - 1) n * packSlots W q y
  have hwin : laurentWindow W q (packSlots W (2 * q - 1) n) (packSlots W q y) =
      P / 2 ^ (W * (q - 1)) % 2 ^ (W * q) := by
    change ((packSlots W (2 * q - 1) n * packSlots W q y) >>> (W * (q - 1))) &&&
      slotMask (W * q) = _
    rw [slotMask_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  rw [hwin]
  have hlt : P / 2 ^ (W * (q - 1)) % 2 ^ (W * q) < 2 ^ (W * q) := Nat.mod_lt _ (by positivity)
  rw [← packSlots_slot hlt]
  refine packSlots_congr fun v hv ↦ ?_
  rw [slot_mod_two_pow hv, slot_div_two_pow]
  exact slot_mul_window_eq_sum hn hy hW hv

/-- With the bounds of `laurentWindow_eq`, and when no slot borrows (`hle`), the applied row is the
packed row of the slots `c0 y_v + cst_v - ∑_u n_{v+q-1-u} y_u`. -/
theorem laurentApply_eq {W q a b c0 : ℕ} {n y cst : ℕ → ℕ}
    (hn : ∀ s < 2 * q - 1, n s ≤ a) (hy : ∀ u < q, y u ≤ b) (hW : (2 * q - 1) * a * b < 2 ^ W)
    (hle : ∀ v < q, ∑ u ∈ range q, n (v + (q - 1) - u) * y u ≤ c0 * y v + cst v) :
    laurentApply W q c0 (packSlots W (2 * q - 1) n) (packSlots W q cst) (packSlots W q y) =
      packSlots W q (fun v ↦ c0 * y v + cst v - ∑ u ∈ range q, n (v + (q - 1) - u) * y u) := by
  unfold laurentApply
  rw [Nat.add_eq, Nat.mul_eq, mul_packSlots, packSlots_add, laurentWindow_eq hn hy hW,
    Nat.sub_eq, packSlots_sub hle]

/-- If the slots of a row are at most `a` and `q a < 2 ^ W`, the middle slot of its product with
the row of ones is the sum of its slots. -/
theorem laurentRowSum_eq {W q a : ℕ} {x : ℕ → ℕ} (hx : ∀ t < q, x t ≤ a)
    (hW : q * a * 1 < 2 ^ W) :
    laurentRowSum W q (packSlots W q x) = ∑ t ∈ range q, x t := by
  rcases Nat.eq_zero_or_pos W with rfl | hW0
  · -- Width zero: `q a = 0`, so every slot is `0`, and so is every slot of width zero.
    have hqa : q * a = 0 := by simpa using hW
    rw [sum_eq_zero fun t ht ↦ by
      have := hx t (mem_range.mp ht)
      rcases Nat.mul_eq_zero.mp hqa with h | h
      · simp [h] at ht
      · omega]
    simp [laurentRowSum, laurentPairSlot, slot_eq, Nat.mod_one]
  unfold laurentRowSum laurentPairSlot
  rw [constSlots_eq hW0, Nat.mul_eq, slot_mul_middle_eq_sum hx (fun _ _ ↦ le_rfl) hW]
  simp

/-- **The Gram value of two rows.** If the rows `x` and `u'` have slots `x_t = c + ξ_t ≤ A` and
`u'_v = d + u_v ≤ B`, and `q A B`, `q A` and `q B` are below `2 ^ W`, the Gram value of the packed
rows is `∑_t ξ_t u_{q-1-t}`. The intended `u'` is the applied row of a row `y_s = c + η_s`, with
`u_v = c0 η_v - ∑_s n_{v+q-1-s} η_s`. -/
theorem laurentGramValue_eq {W q c d A B : ℕ} {x u' : ℕ → ℕ} (ξ u : ℕ → ℤ)
    (hx : ∀ t < q, x t ≤ A) (hu : ∀ v < q, u' v ≤ B) (hW : q * A * B < 2 ^ W)
    (hWA : q * A * 1 < 2 ^ W) (hWB : q * B * 1 < 2 ^ W)
    (hξ : ∀ t < q, (x t : ℤ) = c + ξ t) (hu' : ∀ v < q, (u' v : ℤ) = d + u v) :
    laurentGramValue W q c d (packSlots W q x) (packSlots W q u') =
      ∑ t ∈ range q, ξ t * u (q - 1 - t) := by
  unfold laurentGramValue laurentPairSlot
  rw [Nat.mul_eq, slot_mul_middle_eq_sum hx hu hW, laurentRowSum_eq hx hWA,
    laurentRowSum_eq hu hWB]
  push_cast
  rw [sum_congr rfl fun t ht ↦ by
      rw [hξ t (mem_range.mp ht), hu' (q - 1 - t) (by have := mem_range.mp ht; omega)],
    sum_congr rfl fun t ht ↦ hξ t (mem_range.mp ht),
    sum_congr rfl fun v hv ↦ hu' v (mem_range.mp hv)]
  have hrefl : ∑ t ∈ range q, u (q - 1 - t) = ∑ v ∈ range q, u v := by
    rw [← Finset.sum_range_reflect]
    exact sum_congr rfl fun t ht ↦ by
      rw [show q - 1 - (q - 1 - t) = t by have := mem_range.mp ht; omega]
  simp only [mul_add, add_mul, sum_add_distrib, ← mul_sum, ← sum_mul, hrefl, sum_const,
    card_range, nsmul_eq_mul]
  ring

/-- Removing the bias down to an offset `c ≤ slotBias w`: for entries `f_k` that fit with
`0 ≤ f_k + c`, subtracting the constant row `slotBias w - c` turns the slots `f_k + slotBias w`
into `f_k + c`. -/
theorem biasedPack_sub_offset {w q c : ℕ} {f : ℕ → ℤ} (hw : 0 < w) (hc : c ≤ slotBias w)
    (hfit : ∀ k < q, FitsSlot w (f k)) (hnn : ∀ k < q, 0 ≤ f k + c) :
    biasedPack w q f - constSlots w q (slotBias w - c) =
      packSlots w q (fun k ↦ (f k + c).toNat) := by
  have key := fun k (hk : k < q) ↦ And.intro (encodeSlot_of_fits (hfit k hk)) (hnn k hk)
  rw [biasedPack, constSlots_eq hw, packSlots_sub fun k hk ↦ by have := key k hk; omega]
  exact packSlots_congr fun k hk ↦ by have := key k hk; omega

/-- Two biased rows added and brought down to an offset `c ≤ 2 * slotBias w`: for entries that
fit with `0 ≤ f_k + g_k + c`, the slots of the result are `f_k + g_k + c`. -/
theorem biasedPack_add_sub_offset {w q c : ℕ} {f g : ℕ → ℤ} (hw : 0 < w) (hc : c ≤ 2 * slotBias w)
    (hf : ∀ k < q, FitsSlot w (f k)) (hg : ∀ k < q, FitsSlot w (g k))
    (hnn : ∀ k < q, 0 ≤ f k + g k + c) :
    biasedPack w q f + biasedPack w q g - constSlots w q (2 * slotBias w - c) =
      packSlots w q (fun k ↦ (f k + g k + c).toNat) := by
  have key := fun k (hk : k < q) ↦
    And.intro (encodeSlot_of_fits (hf k hk)) (And.intro (encodeSlot_of_fits (hg k hk)) (hnn k hk))
  rw [biasedPack, biasedPack, packSlots_add, constSlots_eq hw,
    packSlots_sub fun k hk ↦ by have := key k hk; omega]
  exact packSlots_congr fun k hk ↦ by have := key k hk; omega

end CAS.Numerics

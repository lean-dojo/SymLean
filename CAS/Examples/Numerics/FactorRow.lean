/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.FactorRowError
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-!
# The error of a factor row on a table of two by two slots

## Motivation

`CAS.Numerics.abs_sub_factorRow_le` bounds the error of a three-stage factor row for tables of
every size. Besides the slot and the definition of the value, its premises are thirteen
conditions: eight on the tables, and five on the widths, the shift and the bounds of the entries.
Do they hold together on some table, and how far is the bound from the true error on a table
small enough to compute by hand?

## The idea

One data row with the entries `3, -2`, the coefficient `5 - 2 = 3`, the conversion rows `7, -5`
and `4, 9`, the factors `2, -2` and the node rows `10, -20` and `30, 40`. The first stage gives
`H = (9, -6)` and the second `Y = (39, -99)`. The shift by 4 bits takes the floors `2` and `-7`
of `39 / 16` and `-99 / 16`, so slot `0` of the row is `2 * 2 * 10 + (-2) * (-7) * 30 = 460`.
With the scales `2 ^ 3`, `2 ^ 2`, `2 ^ 4` and `2 ^ 1` the exact value is `105 / 16`, and the row
gives `460 / 64`. The kernel checks every premise of the theorem on the tables by evaluation.

## Main results

All of them are about this one table (one example).

* `abs_value_sub_row_le`: both slots of the row are within the bound of the theorem of their
  values.
* `signedSlot_row_zero`, `value_zero`, `bound_zero`, `abs_value_sub_row_zero`: at slot `0` the
  row holds `460`, the value is `105 / 16`, the bound is `5 / 4` and the error is `5 / 8`.

## Relations

* `abs_value_sub_row_le` is `CAS.Numerics.abs_sub_factorRow_le` at these tables.
* `CAS.Numerics.abs_sub_signedSlot_factorRow_le` is the same theorem at 150 data slots, 613
  node slots of 352 bits that are at most `2 ^ 63` in absolute value, and the scales `2 ^ 120`,
  `2 ^ 62` and `2 ^ 62`. Its tables belong to the projects that use it.

## Scope

The bound allows one unit for every floor of the second stage. At slot `0` it is twice the
error. A sharper bound would need the remainders of the shift.
-/

@[expose] public section

namespace CAS.Examples.Numerics.FactorRow

open CAS.Numerics Finset

/-- The data row: the signed entries `3, -2` in two slots of 16 bits. -/
def data : ℕ → ℕ := fun _ ↦ biasedPack 16 2 fun l ↦ if l = 0 then 3 else -2

/-- The mode value `5`, read with the bias `2`: the coefficient `3`. -/
def mode : ℕ → ℕ := fun _ ↦ 5

/-- The conversion rows: the signed entries `7, -5` and `4, 9` in two slots of 24 bits. -/
def conv : ℕ → ℕ := fun l ↦
  biasedPack 24 2 fun k ↦ if l = 0 then (if k = 0 then 7 else -5) else (if k = 0 then 4 else 9)

/-- The node rows: the signed entries `10, -20` and `30, 40` in two slots of 32 bits. -/
def node : ℕ → ℕ := fun k ↦
  biasedPack 32 2 fun n ↦ if k = 0 then (if n = 0 then 10 else -20) else (if n = 0 then 30 else 40)

/-- The positive parts `2, 1` of the integer factors. -/
def cp : ℕ → ℕ := fun k ↦ if k = 0 then 2 else 1

/-- The negative parts `0, 3` of the integer factors, which are `2` and `-2`. -/
def cn : ℕ → ℕ := fun k ↦ if k = 0 then 0 else 3

/-- The factor row of the tables: slots of 16, 24 and 32 bits, a shift by 4 bits, and the
coefficient bias `2 ^ 20`. -/
def row : ℕ := factorRow 16 2 1 2 mode data 24 2 conv 4 32 2 (2 ^ 20) cp cn node

/-- The value that slot `n` of the row approximates: the triple sum with the scales `2 ^ 3`,
`2 ^ 2`, `2 ^ 4` and `2 ^ 1`. -/
noncomputable def value (n : ℕ) : ℝ :=
  ∑ m ∈ range 1, ∑ l ∈ range 2,
    (signedSlot 16 l (data m) : ℝ) / 2 ^ 3 * ((((mode m : ℤ) - (2 : ℕ) : ℤ) : ℝ) / 2 ^ 2) *
      ∑ k ∈ range 2, (signedSlot 24 k (conv l) : ℝ) / 2 ^ 4 *
        (((cp k : ℤ) - cn k : ℤ) : ℝ) * ((signedSlot 32 n (node k) : ℝ) / 2 ^ 1)

/-- Both slots of the row are within the bound of `abs_sub_factorRow_le` of their values. -/
theorem abs_value_sub_row_le {n : ℕ} (hn : n < 2) :
    |value n - (signedSlot 32 n row : ℝ) / 2 ^ (3 + 2 + 1)| ≤
      ∑ k ∈ range 2,
        |(((cp k : ℤ) - cn k : ℤ) : ℝ)| * |(signedSlot 32 n (node k) : ℝ)| / 2 ^ (3 + 2 + 1) :=
  abs_sub_factorRow_le (Db := 3) (Rb := 3) (Kb := 9) (cb := 2) (Gb := 40) (value n) hn rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Slot `0` of the row holds `460`. -/
theorem signedSlot_row_zero : signedSlot 32 0 row = 460 := by
  decide +kernel

/-- The signed entries of the tables. -/
theorem signedSlot_tables :
    signedSlot 16 0 (data 0) = 3 ∧ signedSlot 16 1 (data 0) = -2 ∧
      signedSlot 24 0 (conv 0) = 7 ∧ signedSlot 24 1 (conv 0) = -5 ∧
      signedSlot 24 0 (conv 1) = 4 ∧ signedSlot 24 1 (conv 1) = 9 ∧
      signedSlot 32 0 (node 0) = 10 ∧ signedSlot 32 1 (node 0) = -20 ∧
      signedSlot 32 0 (node 1) = 30 ∧ signedSlot 32 1 (node 1) = 40 := by
  decide +kernel

/-- The value of slot `0` is `105 / 16`. -/
theorem value_zero : value 0 = 105 / 16 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, h9, -⟩ := signedSlot_tables
  simp only [value, sum_range_succ, sum_range_zero, zero_add, h1, h2, h3, h4, h5, h6, h7, h9,
    mode, cp, cn]
  norm_num

/-- At slot `0` the bound of `abs_value_sub_row_le` is `5 / 4`. -/
theorem bound_zero :
    ∑ k ∈ range 2,
      |(((cp k : ℤ) - cn k : ℤ) : ℝ)| * |(signedSlot 32 0 (node k) : ℝ)| / 2 ^ (3 + 2 + 1) =
        5 / 4 := by
  obtain ⟨-, -, -, -, -, -, h7, -, h9, -⟩ := signedSlot_tables
  simp only [sum_range_succ, sum_range_zero, zero_add, h7, h9, cp, cn]
  norm_num

/-- At slot `0` the row is `5 / 8` away from the value, half of the bound. -/
theorem abs_value_sub_row_zero :
    |value 0 - (signedSlot 32 0 row : ℝ) / 2 ^ (3 + 2 + 1)| = 5 / 8 := by
  rw [value_zero, signedSlot_row_zero]
  norm_num [abs_of_neg]

end CAS.Examples.Numerics.FactorRow

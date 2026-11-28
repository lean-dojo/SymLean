/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.ThreeStageRounding
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-!
# The rounding error of a conversion and an evaluation on one entry

## Motivation

`CAS.Numerics.conversion_evaluation_error_le` and `CAS.Numerics.evaluation_error_le` bound the
error of an evaluation in integers for all scales and bounds. Do their premises hold together for
some data, and how far is each bound from the true error on numbers small enough to compute by
hand?

## The idea

One entry, with the scales `2 ^ 4` for the values and `2 ^ 3` for the coefficients. The value
`x = 1 / 5` is held as `X = 3`, since `16 / 5 = 3.2`, and the coefficient `c = 2 / 3` as `C = 5`,
since `16 / 3` is `5.33…`. The converted integer is `Y = ⌊3 * 5 / 8⌋ = 1`. With the mode value
`t = 1` the integer evaluation is `1 * 16 / 256 = 1 / 16`, and the exact value is
`x c t = 2 / 15`. For the evaluation alone, `x = 1 / 5` with `t = 1 / 2` gives `3 * 8 / 256`
against `1 / 10`.

## Main results

All of them are about these numbers (one example each).

* `conversion_bound`: the error of the conversion and evaluation is at most the bound of the
  theorem; `conversion_bound_eq`: that bound is `35 / 192`; `conversion_error`: the error is
  `17 / 240`.
* `evaluation_bound`: the error of the evaluation alone is at most the bound of the theorem;
  `evaluation_bound_eq`: that bound is `1 / 32`; `evaluation_error`: the error is `1 / 160`.

## Relations

* `conversion_bound` is `CAS.Numerics.conversion_evaluation_error_le` at `n = q = 1`, `a = 4`,
  `b = 3` and the bounds `Bx = 3`, `Bc = 2 / 3`, `Bt = 1`.
* `evaluation_bound` is `CAS.Numerics.evaluation_error_le` at `n = 1`, `a = 4` and
  `Bt = 1 / 2`.
* `CAS.Numerics.abs_conversion_evaluation_sub_le` and `CAS.Numerics.abs_evaluation_sub_le` are
  the same theorems at the scales `2 ^ 48` and `2 ^ 80` and the bounds `2 ^ 61`, `2 ^ 10` and
  `2`, the first with a larger constant. Their data belong to the projects that use them.

## Scope

The bounds add the worst case of every rounding. Here they are about two and a half times and
five times the errors.
-/

@[expose] public section

namespace CAS.Examples.Numerics.Rounding

open CAS.Numerics

/-- The value `x = 1 / 5`. -/
noncomputable def value : Fin 1 → ℝ := fun _ ↦ 1 / 5

/-- The integer `3` that holds `2 ^ 4 * x = 3.2`. -/
def stored : Fin 1 → ℤ := fun _ ↦ 3

/-- The conversion coefficient `c = 2 / 3`. -/
noncomputable def coef : Fin 1 → Fin 1 → ℝ := fun _ _ ↦ 2 / 3

/-- The integer `5` that holds `2 ^ 3 * c = 5.33…`. -/
def storedCoef : Fin 1 → Fin 1 → ℤ := fun _ _ ↦ 5

/-- The converted integer `⌊3 * 5 / 2 ^ 3⌋ = 1`. -/
def converted : Fin 1 → ℤ := fun _ ↦ 1

/-- The mode value `t = 1`. -/
noncomputable def mode : Fin 1 → ℝ := fun _ ↦ 1

/-- The mode value `1 / 2` of the evaluation without a conversion. -/
noncomputable def modeHalf : Fin 1 → ℝ := fun _ ↦ 1 / 2

/-- The conversion and evaluation of one entry is within the bound of
`conversion_evaluation_error_le` of the exact value. -/
theorem conversion_bound :
    |(∑ j, (converted j : ℝ) * (2 ^ 4 * mode j)) / 2 ^ (4 + 4) -
        ∑ j, (∑ l, value l * coef l j) * mode j| ≤
      ((1 : ℕ) : ℝ) * 1 *
        (1 / 2 ^ 4 + ((1 : ℕ) : ℝ) * ((2 / 3 + 1) / 2 ^ 4 + (3 + 1) / 2 ^ 4 / 2 ^ (3 + 1))) :=
  conversion_evaluation_error_le (a := 4) (b := 3) (Bx := 3) (Bc := 2 / 3) (Bt := 1) value stored
    coef storedCoef converted mode (by norm_num [value, stored]) (by norm_num [stored])
    (by norm_num [coef, storedCoef]) (by norm_num [coef])
    (by norm_num [stored, storedCoef, converted]) (by norm_num [mode])

/-- The bound of `conversion_bound` is `35 / 192`. -/
theorem conversion_bound_eq :
    ((1 : ℕ) : ℝ) * 1 *
        (1 / 2 ^ 4 + ((1 : ℕ) : ℝ) * ((2 / 3 + 1) / 2 ^ 4 + (3 + 1) / 2 ^ 4 / 2 ^ (3 + 1))) =
      35 / 192 := by
  norm_num

/-- The error of the conversion and evaluation of that entry is `17 / 240`. -/
theorem conversion_error :
    |(∑ j, (converted j : ℝ) * (2 ^ 4 * mode j)) / 2 ^ (4 + 4) -
        ∑ j, (∑ l, value l * coef l j) * mode j| = 17 / 240 := by
  norm_num [converted, mode, value, coef, abs_of_neg]

/-- The evaluation of one entry without a conversion is within the bound of
`evaluation_error_le` of the exact value. -/
theorem evaluation_bound :
    |(∑ l, (stored l : ℝ) * (2 ^ 4 * modeHalf l)) / 2 ^ (4 + 4) - ∑ l, value l * modeHalf l| ≤
      ((1 : ℕ) : ℝ) * (1 / 2) / 2 ^ 4 :=
  evaluation_error_le (a := 4) (Bt := 1 / 2) value stored modeHalf (by norm_num [value, stored])
    (by norm_num [modeHalf])

/-- The bound of `evaluation_bound` is `1 / 32`. -/
theorem evaluation_bound_eq : ((1 : ℕ) : ℝ) * (1 / 2) / 2 ^ 4 = 1 / 32 := by
  norm_num

/-- The error of that evaluation is `1 / 160`. -/
theorem evaluation_error :
    |(∑ l, (stored l : ℝ) * (2 ^ 4 * modeHalf l)) / 2 ^ (4 + 4) - ∑ l, value l * modeHalf l| =
      1 / 160 := by
  norm_num [stored, modeHalf, value, abs_of_neg]

end CAS.Examples.Numerics.Rounding

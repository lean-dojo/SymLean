/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalEval.Registry.Planner

/-!
# Squaring an affine form

For a noise symbol `ε` with `|ε| ≤ 1`, the square of the affine form `1 + ε / 2` is
`1 + ε + ε² / 4`. The affine linearization keeps `1 + ε` and the checked interval
remainder encloses `ε² / 4`. The forms and models are FloatLib's
(`FloatLib.Numerics.Enclosure.Affine`). `shiftedNoise_square_mem` gets the enclosure from
`AffineForm.mulRange`, and `shiftedNoiseModel_square_mem` gets it from the general
multiplication of `AffineModel`, which keeps `ε² ≥ 0`: the two ranges are `[-1/4, 9/4]` and
`[0, 9/4]` (`shiftedNoise_square_ranges`).

The planner's affine route computes the same model. On `x ∈ [1/2, 3/2]`, where
`x = 1 + ε / 2`, `RationalInterval.affineRange?` gives `x * x` the range `[0, 9/4]`
(`square_affineRange`), and `mem_affineRange_of_memBox` turns it into `x * x ≤ 9 / 4`
(`square_le`).
-/

@[expose] public section

namespace CAS.Examples.Numerics.AffineArithmetic

open CAS.Continuum
open FloatLib.Numerics.Enclosure.Affine

/-- The one-noise affine form `1 + ε₀ / 2`. -/
def shiftedNoise : AffineForm :=
  ⟨1, [1 / 2]⟩

/-- The exact affine evaluation is `1 + ε₀ / 2`. -/
theorem shiftedNoise_eval (ε : ℕ → ℝ) :
    shiftedNoise.eval ε = 1 + ε 0 / 2 := by
  simp only [shiftedNoise, AffineForm.eval, AffineForm.dot]
  push_cast
  ring

/-- The checked multiplication enclosure contains every unit-noise square. -/
theorem shiftedNoise_square_mem (ε : ℕ → ℝ)
    (hε : ∀ i, |ε i| ≤ 1) :
    (shiftedNoise.mulRange shiftedNoise).ContainsReal some
      ((1 + ε 0 / 2) ^ 2) := by
  rw [← shiftedNoise_eval, pow_two]
  exact AffineForm.mul_mem_mulRange shiftedNoise shiftedNoise hε

/-- The shifted noise as an exact model with zero remainder. -/
def shiftedNoiseModel : AffineModel :=
  .ofAffine shiftedNoise

/-- General model multiplication represents the square of the represented value. -/
theorem shiftedNoiseModel_square_represents (ε : ℕ → ℝ)
    (hε : ∀ i, |ε i| ≤ 1) :
    (shiftedNoiseModel.mul shiftedNoiseModel).Represents ε
      ((1 + ε 0 / 2) ^ 2) := by
  have hsource : shiftedNoiseModel.Represents ε (1 + ε 0 / 2) := by
    rw [← shiftedNoise_eval]
    exact AffineModel.represents_ofAffine shiftedNoise ε
  simpa [pow_two] using hsource.mul hsource hε

/-- The reported model range contains every represented square. -/
theorem shiftedNoiseModel_square_mem (ε : ℕ → ℝ)
    (hε : ∀ i, |ε i| ≤ 1) :
    (shiftedNoiseModel.mul shiftedNoiseModel).range.ContainsReal some
      ((1 + ε 0 / 2) ^ 2) :=
  AffineModel.mem_range (shiftedNoiseModel_square_represents ε hε) hε

/-- The product of the forms encloses the square in `[-1/4, 9/4]`, and the product of the
models, which keeps `ε² ≥ 0`, in `[0, 9/4]`. The kernel computes both ranges. -/
theorem shiftedNoise_square_ranges :
    shiftedNoise.mulRange shiftedNoise = ⟨-1 / 4, 9 / 4⟩ ∧
      (shiftedNoiseModel.mul shiftedNoiseModel).range = ⟨0, 9 / 4⟩ := by
  decide +kernel

/-- The box `x ∈ [1/2, 3/2]`, on which `x = 1 + ε / 2`. -/
def box : Fin 1 → RationalInterval :=
  fun _ ↦ RationalInterval.ofBounds (1 / 2) (3 / 2) (by norm_num)

/-- The affine route of the planner encloses `x * x` on the box in `[0, 9/4]`, the range of the
model product. The kernel computes it. -/
theorem square_affineRange :
    RationalInterval.affineRange? box (.mul (.var 0) (.var 0)) =
      some (RationalInterval.ofBounds 0 (9 / 4) (by norm_num)) := by
  decide +kernel

/-- `x * x ≤ 9 / 4` for `x ∈ [1/2, 3/2]`, from the affine range. -/
theorem square_le (x : ℝ) (h0 : 1 / 2 ≤ x) (h1 : x ≤ 3 / 2) : x * x ≤ 9 / 4 := by
  have hx : ∀ i, (box i).MemReal x := fun _ ↦
    RationalInterval.memReal_ofBounds _ ⟨by norm_num [h0], by norm_num [h1]⟩
  simpa [RationalInterval.ofBounds] using
    (RationalInterval.mem_affineRange_of_memBox box _ _ (fun _ ↦ x) hx square_affineRange).2

end CAS.Examples.Numerics.AffineArithmetic

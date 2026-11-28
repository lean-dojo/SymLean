/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Expr.FloatLib
public import CAS.Expr.Operators
public import FloatLib.Numerics.Enclosure.Expression.BackendsProof

/-!
# FloatLib on translated expressions, by hand

These examples use the translation of `CAS.Expr.FloatLib` without `cega`. Most of them translate
an expression with `Expr.toFloatLib`, let the kernel run one of FloatLib's interval evaluations or
checks on it (`decide +kernel`), and read the result back with `Expr.containsReal_evalZero?` or
`Expr.holds_of_checkZero`. The backend is FloatLib's exact rational one with its standard calls,
at the default settings: 64 bits and degree 16.

First we look at how the translation writes `π`, `e`, real powers and the clamped arguments of
`sqrt`, `asin` and `acos`. Then FloatLib bounds an expression with every constructor on a box,
encloses `π` and a real power at a variable positive base, and proves bounds that need the clamps:
without them, its square root and inverse sine reject argument intervals that leave their domain.
Numbering by occurrence handles labels of any type. The last example lowers `1 / x` with the bound
`1/2 ≤ |x|`. FloatLib cannot divide by the interval `[-1, 1]` of `x`, but it can multiply by the
interval `[-2, 2]` of the fresh input for `x⁻¹`.
-/

@[expose] public section

namespace CAS.Examples.CEGA.Translate

open CAS.Verified FloatLib.Numerics FloatLib.Numerics.Interval

/-! ## How the translation writes each operation -/

/-- `π` and `e` are the calls `0` and `2` of FloatLib's standard calls. -/
example : (Expr.add .pi .e : Expr ℕ).toFloatLib id =
    .binary .add (.call 0 []) (.call 2 []) := rfl

/-- The real power `x ^ y` is the call `1`, with the base and the exponent as its arguments. -/
example : (Expr.rpow (.var 0) (.var 1) : Expr ℕ).toFloatLib id = .call 1 [.var 0, .var 1] :=
  rfl

/-- The argument of the square root goes through `max 0`. -/
example : (Expr.sqrt (.var 0) : Expr ℕ).toFloatLib id =
    .unary .sqrt (.binary .max (.const 0) (.var 0)) := rfl

/-- The arguments of `asin` and `acos` go through `max (-1) (min 1 _)`. -/
example : (Expr.acos (.var 0) : Expr ℕ).toFloatLib id =
    .unary .acos (.binary .max (.const (-1)) (.binary .min (.const 1) (.var 0))) := rfl

/-! ## Every constructor -/

/-- An expression with every constructor of `Verified.Expr`, in `x = var 0` and `y = var 1`:
`2 + (-3) + 1/3 + (π - e) + x y / (y - x) - x² + sin x + cos y + atan y + asin (2 y) + acos x +
exp x + log y + √(x - 1) + y ^ x`. On the box `[1/4, 1/2] × [1, 2]` the argument `2 y` of the
inverse sine is above `1` and the argument `x - 1` of the square root is negative, so both clamps
act. -/
def everyConstructor : Expr ℕ :=
  2 + .int (-3) + .rat 1 3 + (.pi - .e) + .var 0 * .var 1 / (.var 1 - .var 0) +
    -(.var 0 ^ 2) + .sin (.var 0) + .cos (.var 1) + .atan (.var 1) + .asin (2 * .var 1) +
    .acos (.var 0) + .exp (.var 0) + .log (.var 1) + .sqrt (.var 0 - 1) +
    .rpow (.var 1) (.var 0)

/-- FloatLib bounds `everyConstructor` by `11` on the box `[1/4, 1/2] × [1, 2]`, with one
evaluation and no subdivision. Its enclosure is about `[5.15, 10.51]`. -/
example (ρ : ℕ → ℝ) (hx : ρ 0 ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) (hy : ρ 1 ∈ Set.Icc (1 : ℝ) 2) :
    everyConstructor.eval ρ ≤ 11 := by
  have h := Expr.holds_of_checkZero (Backend.rational_sound {}) (config := {}) (vars := id)
    (values := ρ) (fun _ ↦ rfl) (relation := .nonpositive) (box := [⟨1 / 4, 1 / 2⟩, ⟨1, 2⟩])
    (depth := 0) (everyConstructor - .nat 11) (by decide +kernel)
    (by simpa using And.intro hx hy)
  simpa [Relation.Holds] using h

/-! ## `π` and real powers -/

/-- `3 < π < 22/7`, from FloatLib's enclosure of `π`, the call `0`, on the empty box. -/
example : 3 < Real.pi ∧ Real.pi < 22 / 7 := by
  have lower := Expr.holds_of_checkZero (Backend.rational_sound {}) (config := {})
    (vars := (id : ℕ → ℕ)) (values := fun _ ↦ 0) (fun _ ↦ rfl) (relation := .negative)
    (box := []) (depth := 0) (.sub (.nat 3) .pi) (by decide +kernel) (Box.containsReal_nil _)
  have upper := Expr.holds_of_checkZero (Backend.rational_sound {}) (config := {})
    (vars := (id : ℕ → ℕ)) (values := fun _ ↦ 0) (fun _ ↦ rfl) (relation := .negative)
    (box := []) (depth := 0) (.sub .pi (.rat 22 7)) (by decide +kernel) (Box.containsReal_nil _)
  constructor
  · simpa [Relation.Holds] using lower
  · simpa [Relation.Holds] using upper

/-- A real power at a variable positive base, the call `1`: `y ^ (1/2) ≤ 3/2` for `y ∈ [1, 2]`. -/
example (y : ℝ) (hy : y ∈ Set.Icc (1 : ℝ) 2) : y ^ (1 / 2 : ℝ) ≤ 3 / 2 := by
  have h := Expr.holds_of_checkZero (Backend.rational_sound {}) (config := {}) (vars := id)
    (values := fun _ ↦ y) (fun _ ↦ rfl) (relation := .nonpositive) (box := [⟨1, 2⟩])
    (depth := 0) (.sub (.rpow (.var 0) (.rat 1 2)) (.rat 3 2)) (by decide +kernel)
    (by simpa using hy)
  simpa [Relation.Holds] using h

/-! ## The clamps -/

/-- Without its clamp, FloatLib's square root rejects the argument interval `[-1, 1]`. -/
example : (Interval.Expr.unary .sqrt (.var 0)).evalZero?
    ((Backend.rational {}).withExtensions {} Backend.Standard.extensions)
    (fun _ ↦ some ⟨-1, 1⟩) = none := by
  decide +kernel

/-- With it, `√x ≤ 1` for every `x ∈ [-1, 1]`, where Mathlib's square root is `0` below `0`. -/
example (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) : Real.sqrt x ≤ 1 := by
  have h := Expr.holds_of_checkZero (Backend.rational_sound {}) (config := {}) (vars := id)
    (values := fun _ ↦ x) (fun _ ↦ rfl) (relation := .nonpositive) (box := [⟨-1, 1⟩])
    (depth := 0) (.sub (.sqrt (.var 0)) (.nat 1)) (by decide +kernel) (by simpa using hx)
  simpa [Relation.Holds] using h

/-- Without its clamp, FloatLib's inverse sine rejects the argument interval `[0, 2]`. -/
example : (Interval.Expr.unary .asin (.var 0)).evalZero?
    ((Backend.rational {}).withExtensions {} Backend.Standard.extensions)
    (fun _ ↦ some ⟨0, 2⟩) = none := by
  decide +kernel

/-- With the clamps, `asin x ≤ 8/5` for `x ∈ [0, 2]` and `acos x ≤ 16/5` for `x ∈ [-2, 0]`,
where Mathlib's inverse sine and cosine are constant outside `[-1, 1]`. -/
example (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 2) (z : ℝ) (hz : z ∈ Set.Icc (-2 : ℝ) 0) :
    Real.arcsin x ≤ 8 / 5 ∧ Real.arccos z ≤ 16 / 5 := by
  have hasin := Expr.holds_of_checkZero (Backend.rational_sound {}) (config := {}) (vars := id)
    (values := fun _ ↦ x) (fun _ ↦ rfl) (relation := .nonpositive) (box := [⟨0, 2⟩])
    (depth := 0) (.sub (.asin (.var 0)) (.rat 8 5)) (by decide +kernel) (by simpa using hx)
  have hacos := Expr.holds_of_checkZero (Backend.rational_sound {}) (config := {}) (vars := id)
    (values := fun _ ↦ z) (fun _ ↦ rfl) (relation := .nonpositive) (box := [⟨-2, 0⟩])
    (depth := 0) (.sub (.acos (.var 0)) (.rat 16 5)) (by decide +kernel) (by simpa using hz)
  constructor
  · simpa [Relation.Holds] using hasin
  · simpa [Relation.Holds] using hacos

/-! ## Numbering by occurrence -/

/-- The two occurrences of `x` in `x * x` get the inputs `0` and `1`. The labels are strings, and
no equality of labels is decided. -/
example : (Expr.mul (.var "x") (.var "x") : Expr String).numberOccurrences 0 =
    .mul (.var 0) (.var 1) ∧
    (Expr.mul (.var "x") (.var "x") : Expr String).occurrences = ["x", "x"] :=
  ⟨rfl, rfl⟩

/-- `x * x ≤ 4` for `x ∈ [1, 2]`: FloatLib evaluates the numbered expression on the box that
gives both occurrences the interval `[1, 2]` of `x`. -/
example (x : ℝ) (hx : x ∈ Set.Icc (1 : ℝ) 2) :
    (Expr.mul (.var "x") (.var "x") : Expr String).eval (fun _ ↦ x) ≤ 4 := by
  have hbox := Expr.containsReal_occurrences (intervals := fun _ ↦ ⟨1, 2⟩) (ρ := fun _ ↦ x)
    (expr := (Expr.mul (.var "x") (.var "x") : Expr String)) fun _ _ ↦ by simpa using hx
  have h := Expr.containsReal_evalZero?_numberOccurrences (Backend.rational_sound {})
    (config := {}) hbox (I := ⟨1, 4⟩) (by decide +kernel)
  simpa using ((containsReal_some_iff _ _).1 h).2

/-! ## A quotient with a known denominator bound -/

/-- The bound `1/2 ≤ |x|` of the denominator `x = var 0`, as a chart could prove it. -/
def halfBound (b : Expr ℕ) : Option ℚ :=
  if b = .var 0 then some (1 / 2) else none

/-- Lowering `1 / x` with that bound gives `1 * w`, where the fresh input `w` stands for `x⁻¹`. -/
example : (Expr.div (.nat 1) (.var 0) : Expr ℕ).lowerDivisions halfBound =
    .mul (.nat 1) (.var (.inr (.var 0, 1 / 2))) := rfl

/-- FloatLib cannot divide by the interval `[-1, 1]`. -/
example : ((Expr.div (.nat 1) (.var 0) : Expr ℕ).toFloatLib id).evalZero?
    ((Backend.rational {}).withExtensions {} Backend.Standard.extensions)
    (fun _ ↦ some ⟨-1, 1⟩) = none := by
  decide +kernel

/-- With the bound, FloatLib encloses `1 / x` in `[-2, 2]` at every `x ∈ [-1, 1]` with
`1/2 ≤ |x|`: the lowered expression multiplies by the fresh input, whose interval is `[-2, 2]`. -/
example (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hδ : 1 / 2 ≤ |x|) :
    -2 ≤ 1 / x ∧ 1 / x ≤ 2 := by
  have hbox := Expr.containsReal_occurrences
    (intervals := Expr.loweredIntervals fun _ ↦ ⟨-1, 1⟩) (ρ := Expr.loweredValues fun _ ↦ x)
    (expr := (Expr.div (.nat 1) (.var 0) : Expr ℕ).lowerDivisions halfBound)
    (Expr.containsReal_loweredIntervals (fun _ _ ↦ by simpa using hx) fun b δ hb ↦ by
      unfold halfBound at hb
      split_ifs at hb with hb0
      cases hb
      subst hb0
      exact ⟨by norm_num, by simpa using hδ⟩)
  have h := Expr.containsReal_evalZero?_numberOccurrences (Backend.rational_sound {})
    (config := {}) hbox (I := ⟨-2, 2⟩) (by decide +kernel)
  rw [Expr.eval_lowerDivisions] at h
  simpa using (containsReal_some_iff _ _).1 h

end CAS.Examples.CEGA.Translate

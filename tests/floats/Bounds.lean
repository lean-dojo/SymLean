/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
import CAS

/-!
# Bounds of a package that does not name its arithmetic

The module of the packages of `tests/floats`. The first five theorems call `cega` without a word
about the arithmetic, so they compute in the arithmetic of the build: exact rationals by default,
and the format of the option `cega.arithmetic` when the lakefile or the command line sets it. The
next four choose for themselves, and keep their choice in every build. The last three do not
depend on the build either: a bound on an integral asks for exact rationals, a finite statement
is decided as it is written, and `cas` computes with exact rationals.
-/

/-- Bare `cega` on a box. -/
theorem bare (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.72 := by
  cega

/-- Bare `cega` on a closed goal. -/
theorem closed : Real.sqrt 2 ≤ 1.415 := by
  cega

/-- Bare `cega` with a depth. -/
theorem configured (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : x * (1 - x) ≤ 0.26 := by
  cega (depth := 6)

/-- The explicit query. -/
theorem query (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.73 := by
  cega [enclose x in [0, 1]] (Real.exp x)

/-- `cega [fast]`, which is bare `cega` in the kernel profile. -/
theorem fast (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.74 := by
  cega [fast]

/-- A call that asks for exact arithmetic. -/
theorem floatsOff (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.75 := by
  cega [use_floats := false]

/-- A call that asks for floats: binary64, or the format of the build. -/
theorem floatsOn (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.76 := by
  cega [use_floats := true]

/-- A call that names its format. -/
theorem quad (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.77 := by
  cega (arith := binary128)

/-- An explicit query that asks for exact arithmetic. -/
theorem queryExact (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.78 := by
  cega (arith := "exact") [enclose x in [0, 1]] (Real.exp x)

/-- A bound on an integral, which is computed with exact rationals. -/
theorem integral : (∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) ≤ 3 / 4 := by
  cega [use_floats := false]

/-- A finite statement. -/
theorem finite : ∀ i : Fin 6, i.val < 6 := by
  cega

/-- The box route of `cas`. -/
theorem viaCas (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.79 := by
  cas

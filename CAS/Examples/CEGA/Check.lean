/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.CEGA.FloatQuery
public import CAS.Expr.Operators

/-!
# FloatLib's queries by hand

These examples use `CAS.CEGA.Check` without `cega`. Each builds a query or a check of FloatLib on a
box, lets the kernel evaluate it (`decide +kernel`), and turns the result into a statement about
real numbers with the theorem that `cega` would apply: `boundOn_of_check` or
`enclosedOn_of_check` of `CAS.CEGA.Query` for a query of `Check.enclose?`, and
`Check.holdsOn_of_checkZero` for a Boolean check.

A query returns one enclosure of the expression on the whole box, which the stated bounds are
then compared with. A check compares FloatLib's enclosure with zero, and when that is not enough it
cuts the box in two and checks both halves, up to a given depth. So `x * (1 - x) ≤ 0.26` on
`[0, 1]`, whose natural enclosure on the whole box is `[0, 1]`, needs a check of depth 6, where
the pieces have width `1 / 64`. The same calls run with exact rationals, on FloatLib's binary
grid, with the backend of `cega`'s certified evaluation and with binary64 floats, and one check
goes through FloatLib's own theorem to show what `Check.holdsOn_of_checkZero` adds. Then come the
float query of `CAS.CEGA.FloatQuery`, whose ends are binary64 numbers, and what
`Check.obstruction?` and `floatObstruction?` report for queries without a result.
-/

@[expose] public section

namespace CAS.Examples.CEGA.Check

open CAS.Certificate CAS.Continuum CAS.Continuum.RationalInterval CAS.Verified
open CAS.CEGA CAS.CEGA.Check
open FloatLib.Numerics.Interval (Relation Obstruction)
open FloatLib.Floats.Formats.BinaryInterchange

set_option linter.hashCommand false

/-- The box `[0, 1]`. -/
def unitBox : Fin 1 → RationalInterval := fun _ ↦ .ofBounds 0 1 (by norm_num)

/-- The box `[0, 1] × [2, 3]`. -/
def rectangle : Fin 2 → RationalInterval :=
  ![.ofBounds 0 1 (by norm_num), .ofBounds 2 3 (by norm_num)]

/-! ## Queries -/

/-- `x * y ≤ 3` on `[0, 1] × [2, 3]`. FloatLib's exact evaluation of `x * y` on the box is
`[0, 3]`, and `boundOn_of_check` turns the kernel's comparison of its upper end with `3` into the
bound. -/
theorem mul_le : ∀ p ∈ boxDomain rectangle, p 0 * p 1 ≤ (3 : ℝ) := by
  have h := boundOn_of_check (Check.enclose? .rational {} rectangle (.var 0 * .var 1)) 3
    (by decide +kernel)
  intro p hp
  simpa using h p hp

/-- The same bound on FloatLib's binary grid of `2 ^ (-64)`, whose ends are integers: the product
of two grid intervals is computed in integer arithmetic. -/
example : ∀ p ∈ boxDomain rectangle, p 0 * p 1 ≤ (3 : ℝ) := by
  have h := boundOn_of_check (Check.enclose? .binaryGrid {} rectangle (.var 0 * .var 1)) 3
    (by decide +kernel)
  intro p hp
  simpa using h p hp

/-- `0 ≤ x / (1 + x) ≤ 1` on `[0, 1]`, by the enclosure `[0, 1]` that FloatLib computes. -/
theorem div_mem : ∀ p ∈ boxDomain unitBox, p 0 / (1 + p 0) ∈ Set.Icc (0 : ℝ) 1 := by
  have h := enclosedOn_of_check (Check.enclose? .rational {} unitBox (.var 0 / (1 + .var 0)))
    0 1 (by decide +kernel)
  intro p hp
  simpa using h p hp

/-- `exp x ≤ 2.72` on `[0, 1]`, with the backend of `cega`'s certified evaluation at the default
precision policy and the settings `Precision.toConfig` that its evaluation context uses. -/
theorem exp_le : ∀ p ∈ boxDomain unitBox, Real.exp (p 0) ≤ 2.72 := by
  have h := boundOn_of_check
    (Check.enclose? (.exact {}) (Precision.toConfig {}) unitBox (.exp (.var 0))) (68 / 25)
    (by decide +kernel)
  intro p hp
  have := h p hp
  norm_num at this ⊢
  linarith

/-- The same bound in binary64: every operation is rounded outward to binary64 numbers, and the
two ends of the enclosure are binary64 numbers. -/
theorem exp_le_binary64 : ∀ p ∈ boxDomain unitBox, Real.exp (p 0) ≤ 2.72 := by
  have h := boundOn_of_check
    (Check.enclose? (.binary .binary64) (floatConfig .binary64) unitBox (.exp (.var 0)))
    (68 / 25) (by decide +kernel)
  intro p hp
  have := h p hp
  norm_num at this ⊢
  linarith

/-! ## Checks -/

/-- `x * (1 - x) ≤ 0.26` on `[0, 1]`, by FloatLib's check of `x * (1 - x) - 13/50 ≤ 0`, which
cuts the box into pieces of width `1 / 64`. -/
theorem parabola_le : ∀ p ∈ boxDomain unitBox, p 0 * (1 - p 0) ≤ (0.26 : ℝ) := by
  have h := holdsOn_of_checkZero .rational {} (box := unitBox) (relation := .nonpositive)
    (expr := .var 0 * (1 - .var 0) - .rat 13 50) (depth := 6) (by decide +kernel)
  intro p hp
  have := h p hp
  norm_num [Relation.Holds] at this ⊢
  linarith

/-- `exp x < 3` on `[0, 1]`, a strict bound: the relation is `negative`. -/
theorem exp_lt : ∀ p ∈ boxDomain unitBox, Real.exp (p 0) < 3 := by
  have h := holdsOn_of_checkZero .rational {} (box := unitBox) (relation := .negative)
    (expr := .exp (.var 0) - 3) (depth := 0) (by decide +kernel)
  intro p hp
  have := h p hp
  norm_num [Relation.Holds] at this
  linarith

/-- `π < 22 / 7`, by FloatLib's own theorem: `Check.holdsOn_of_checkZero` is FloatLib's
`Expr.checkZero_sound` for the backend with the standard calls (`Endpoints.backend_sound`), read
back by `Verified.Expr.eval_toFloatLib`. Here the box is empty and `π` is the call `0`. -/
example : Real.pi < 22 / 7 := by
  have h := (Verified.Expr.toFloatLib Fin.val (.pi - .rat 22 7 : Expr (Fin 0))).checkZero_sound
    (Endpoints.rational.backend_sound {}) (relation := .negative) (box := []) (depth := 0)
    (by decide +kernel) (FloatLib.Numerics.Interval.Box.containsReal_nil fun _ ↦ 0)
  rw [Verified.Expr.eval_toFloatLib _ Fin.val Fin.elim0 _ fun i ↦ i.elim0] at h
  norm_num [Relation.Holds] at h
  linarith

/-! ## A float query -/

/-- The float query of `x * (1 - x)` on `[0, 1]` in binary64 has a result: its diagnosis reports
nothing (`encloseBoxFloat?_isSome_iff`). -/
theorem parabola_isSome :
    (encloseBoxFloat? .binary64 rfl [] unitBox (.var 0 * (1 - .var 0))).isSome = true :=
  encloseBoxFloat?_isSome_iff.mpr (by decide +kernel)

/-- The two ends of that result are finite binary64 numbers (`ends_of_encloseBoxFloat?`). -/
example : ∃ a, encloseBoxFloat? .binary64 rfl [] unitBox (.var 0 * (1 - .var 0)) = some a ∧
    ∃ l u : Model FloatFormat.binary64, Model.isFinite l = true ∧ Model.isFinite u = true ∧
      (a.interval.lo : ℝ) = Model.toReal l ∧ (a.interval.hi : ℝ) = Model.toReal u := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp parabola_isSome
  exact ⟨a, ha, ends_of_encloseBoxFloat? ha⟩

/-! ## Queries without a result -/

/-- FloatLib cannot divide by the interval `[0, 1]` of `x`, so the query of `1 / x` on `[0, 1]`
has no result, and the diagnosis names the quotient and its two input intervals. -/
example : Check.obstruction? .rational {} unitBox (1 / .var 0) =
    some (.rejected (.binary .div (.const 1) (.var 0)) [⟨1, 1⟩, ⟨0, 1⟩]) := by
  decide +kernel

/-- A query with a result has nothing to report (`Check.obstruction?_eq_none_iff`). -/
example : Check.obstruction? .rational {} unitBox (.var 0 / (1 + .var 0)) = none := by
  decide +kernel

/-- `10 ^ 39` is past the largest binary32 number, so a box with that bound has no binary32
enclosure, and the diagnosis names its coordinate. -/
example : floatObstruction? .binary32 [] (fun _ : Fin 1 ↦ .ofBounds 0 (10 ^ 39) (by norm_num))
    (.var 0) = some (.missingVariable 0) := by
  decide +kernel

/--
info: 'CAS.Examples.CEGA.Check.parabola_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms parabola_le

/--
info: 'CAS.Examples.CEGA.Check.exp_le_binary64' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms exp_le_binary64

end CAS.Examples.CEGA.Check

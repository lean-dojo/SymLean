/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
import CAS.Examples.Cert.Structure
import CAS.Examples.Cert.Mesh

/-!
# What the certificate commands refuse

Each command of `CAS.Cert` fails on a statement that its test does not establish, and a tactic
that splits a structure leaves an undecided field as a goal. `#guard_msgs` pins the messages, so
an elaboration of this file without errors is the test; `tests/cert/run.sh` runs it.
-/

open CAS.Cert CAS.Numerics CAS.Examples.Cert

set_option linter.hashCommand false

/-! ### Relations and intervals -/

-- A false relation.
/-- error: cert_scalar: the test failed. -/
#guard_msgs (error, substring := true) in
example : Real.sqrt 2 ≤ 1 := by cert_scalar

-- A true relation without a gap between irrational numbers is not decided.
/-- error: cert_scalar: the test failed. -/
#guard_msgs (error, substring := true) in
example : Real.sqrt 2 ≤ Real.sqrt 2 := by cert_scalar

-- The same relation between rational numbers is decided by their exact values.
example : (1 : ℝ) / 3 + 1 / 6 ≤ 1 / 2 := by cert_scalar
example : (1 : ℝ) / 3 + 1 / 6 = 1 / 2 := by cert_scalar

-- A false statement on an interval: the bound fails near `x = 1`.
/-- error: cert_cond: the test failed. -/
#guard_msgs (error, substring := true) in
example : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → x ^ 2 ≤ 9 / 10 := by cert_cond 64 depth 3

-- A true one, on an interval and on a box.
example : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → x ^ 2 ≤ 1 + 1 / 1000 := by cert_cond
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1, |x * y| ≤ 1 + 1 / 100 := by cert_cond
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ x + 1 / 100 ∧ Real.cos x ≤ 1 + 1 / 100 := by
  cert_cond 64

-- A bound that depends on its own variable is not an interval.
/-- error: cert_cond: a bound of `x` depends on `x` -/
#guard_msgs (error, substring := true) in
example : ∀ x : ℝ, x ≤ x → x ≤ 1 → x ≤ 2 := by cert_cond

-- A variable that no interval bounds is not a condition.
/-- error: cert_cond: `x` is not bounded -/
#guard_msgs (error, substring := true) in
example : ∀ x : ℝ, 0 ≤ x → x ^ 2 ≤ 1 := by cert_cond

/-! ### What the tactics read

One passing statement for each form that the docstring of `cert_cond` names and that no example
of the library uses. -/

-- A logarithm, an arctangent, an arcsine and an arccosine.
example : Real.log 2 ≤ 7 / 10 := by cert_scalar
example : Real.arctan 1 ≤ 4 / 5 := by cert_scalar
example : Real.arcsin (1 / 2) ≤ 53 / 100 := by cert_scalar
example : Real.arccos (1 / 2) ≤ 21 / 20 := by cert_scalar

-- A maximum, a minimum, a reciprocal and decimal literals.
example : max (1 : ℝ) 2 ≤ 3 := by cert_scalar
example : min (1 : ℝ) 2 ≤ 3 / 2 := by cert_scalar
example : (3 : ℝ)⁻¹ ≤ 0.34 := by cert_scalar
example : (0.5 : ℝ) + 0.25 = 0.75 := by cert_scalar

-- An equality of numbers on the grid, a disjunction, and the cast of a natural number.
example : (2 : ℝ) + 2 = 4 := by cert_scalar
example : Real.sqrt 2 ≤ 1 ∨ Real.sqrt 2 ≤ 3 / 2 := by cert_cond
example : ((7 : ℕ) : ℝ) / 2 ≤ 4 := by cert_scalar

-- `Cond.all`: the square of `k / 8` is at most `5 / 4` for every `k < 9`. With the bound `1`
-- the test fails at `k = 8`, where the two sides are equal and the product is rounded.
example : (Cond.all 9 fun k ↦ .le (.pow (.rat k 8) 2) (.rat 5 4) : Cond Empty).run 64 Empty.elim =
    true := by
  cert_eval

/-- error: CEGA finite certificate could not certify a checked computation -/
#guard_msgs (error, substring := true) in
example : (Cond.all 9 fun k ↦ .le (.pow (.rat k 8) 2) (.nat 1) : Cond Empty).run 64 Empty.elim =
    true := by
  cert_eval

-- A name in the list of `cert_eval` that is no constant is an error, not a slower evaluation.
/-- error: Unknown constant `noSuchDefinition` -/
#guard_msgs (error, substring := true) in
example : Nat.ble 1 2 = true := by cert_eval [noSuchDefinition]

/-! ### Structures of conditions -/

open Structure in
-- The open fields must be the expected ones.
/--
error: cert_reduce: the open fields are [f_le, f_cont, mass] and not [f_le]
-/
#guard_msgs in
cert_reduce wrong (leaving := [f_le]) : Profile datum

open Structure in
-- A field that the test does not decide stays a goal: the tactic leaves exactly three.
#guard_msgs (drop info) in
example (h1 : ∀ x, datum.f x ≤ datum.ν) (h2 : Continuous datum.f)
    (h3 : ∫ x in (0 : ℝ)..1, datum.f x = datum.r) : Profile datum := by
  cert_fields
  · exact h1
  · exact h2
  · exact h3

-- A statement with a universe parameter is refused: the theorem would have none.
universe u in
/-- error: cert_reduce: the statement has universe parameters -/
#guard_msgs (error, substring := true) in
cert_reduce poly : Nonempty (ULift.{u, 0} Unit)

/-- A structure whose second field mentions the proof of its first. -/
structure Dependent : Prop where
  /-- A fact that no test decides. -/
  cont : Continuous fun x : ℝ ↦ x
  /-- A fact whose statement mentions the first field. -/
  again : cont = cont → Continuous fun x : ℝ ↦ x + 1

-- Open fields become hypotheses one by one, so a field that mentions another is refused.
/-- error: cert_reduce: the field `again` depends on another field -/
#guard_msgs (error, substring := true) in
cert_reduce dependent : Dependent

-- A goal that is not a structure is not split: `constructor` would choose a case of `∨`.
/-- error: cert_fields: the goal is not a structure -/
#guard_msgs (error, substring := true) in
example : (1 : ℝ) < 0 ∨ (0 : ℝ) < 1 := by cert_fields

/-! ### Ranges and data -/

/-- A family that fails at index `5`. -/
def failsAt5 (k : ℕ) : Bool := Bool.rec true false (Nat.beq k 5)

cert_shard low : failsAt5 (below := 8) (start := 0) (count := 5)
cert_shard high : failsAt5 (below := 8) (start := 6) (count := 2)

-- A range that contains the failing index is refused: the kernel evaluates its loop to `false`.
/-- error: CEGA finite certificate could not certify a checked computation: the kernel did not reduce the decision procedure of -/
#guard_msgs (error, substring := true) in
cert_shard bad : failsAt5 (below := 8) (start := 0) (count := 8)

-- A batch of no index is refused.
/-- error: a batch holds at least one index -/
#guard_msgs in
cert_shard none : failsAt5 (below := 8) (start := 0) (count := 5) (batch := 0)

-- A range past the end is refused.
/-- error: the range ends at 9, after 8 -/
#guard_msgs in
cert_shard past : failsAt5 (below := 8) (start := 6) (count := 3)

/-- A second name for the first range, so that the two ranges are numbered `0` and `1`. -/
theorem part0 : RangeAll (fun j : Fin 8 ↦ failsAt5 j.val = true) 0 5 := low

/-- A second name for the second range. -/
theorem part1 : RangeAll (fun j : Fin 8 ↦ failsAt5 j.val = true) 6 2 := high

-- Ranges with a gap are not joined: index `5` is in neither.
/-- error: part1 starts at 6, but the ranges before it end at 5 -/
#guard_msgs in
cert_aggregate joined : failsAt5 (below := 8) (shards := part, 2)

-- Ranges that stop before the end are not joined either.
/-- error: the 1 ranges end at 5, not at 8 -/
#guard_msgs in
cert_aggregate short : failsAt5 (below := 8) (shards := part, 1)

-- A text with another digest, and a text with another length.
/--
error: the SHA-256 digest of the text is 12ee7318138f3116c9843fad669f5d73822e6bbf6154b906ea15cb9b3f89ad8c, not 0000000000000000000000000000000000000000000000000000000000000000
-/
#guard_msgs in
example : ℕ → ℕ :=
  pinned_hex% 64 4 1 17 "0000000000000000000000000000000000000000000000000000000000000000"
    "0000010000000000\n"

/-- error: the text has 17 bytes, not 16 -/
#guard_msgs in
example : ℕ → ℕ :=
  pinned_hex% 64 4 1 16 "12ee7318138f3116c9843fad669f5d73822e6bbf6154b906ea15cb9b3f89ad8c"
    "0000010000000000\n"

-- A text that is not one entry per line: two entries on one line, and a byte that is no digit.
/-- error: line 0 of the text is not 16 hexadecimal digits and a line feed -/
#guard_msgs in
example : ℕ → ℕ :=
  pinned_hex% 64 4 2 34 "245aed74df135c74dd16a258fe91448db25f3b29bd995786dc36a531ace6093e"
    "0000010000000000 0000010000000000\n"

/-- error: line 0 of the text is not 16 hexadecimal digits and a line feed -/
#guard_msgs in
example : ℕ → ℕ :=
  pinned_hex% 64 4 1 17 "e1db37024c00c8fc9a9ce9e003c1f68e6dd03c79bf88f66a3ba3d9fd1a70c6ae"
    "000001000000000g\n"

-- A text of fewer lines than the module says.
/-- error: the text has 17 bytes, not 2 lines of 16 digits and a line feed -/
#guard_msgs in
example : ℕ → ℕ :=
  pinned_hex% 64 4 2 17 "12ee7318138f3116c9843fad669f5d73822e6bbf6154b906ea15cb9b3f89ad8c"
    "0000010000000000\n"

-- One function reads a line for the build and for a run: a line in the format, a line that
-- ends early, a byte that is no digit, and a width that is not a multiple of 4.
#guard hexEntry? 8 ⟨#[56, 49, 10]⟩ 0 = some 1
#guard hexEntry? 8 ⟨#[56, 49, 10, 55, 102, 10]⟩ 1 = some 255
#guard hexEntry? 8 ⟨#[56, 49]⟩ 0 = none
#guard hexEntry? 8 ⟨#[56, 103, 10]⟩ 0 = none
#guard hexEntry? 8 ⟨#[56, 49, 32]⟩ 0 = none
#guard hexEntry? 6 ⟨#[56, 10]⟩ 0 = none
#guard hexEntry? 0 ⟨#[10]⟩ 0 = none

-- A tree over more terms than one definition holds: 40 numbers, read back in the kernel.
example : ∀ j, j < 40 → (nat_tree% [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17,
    18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]) j =
      j := by
  decide +kernel

/-- error: nat_tree% needs at least one part -/
#guard_msgs in
example : ℕ → ℕ := nat_tree% []

/-! ### What the examples rest on -/

/-- info: 'CAS.Examples.Cert.Mesh.cubic_le_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Mesh.cubic_le_bound

/-- info: 'CAS.Examples.Cert.Mesh.nonempty_of_tiny_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Mesh.nonempty_of_tiny_run

/-- info: 'CAS.Examples.Cert.MeshSpec.cells_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MeshSpec.cells_of_run

/-- info: 'CAS.Examples.Cert.Mesh.run_look' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Mesh.run_look

/-- info: 'CAS.Examples.Cert.Mesh.run_cubic_le_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Mesh.run_cubic_le_bound

/-- info: 'CAS.Examples.Cert.Structure.profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Structure.profile

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Cert.Cond
public import CAS.Numerics.SlotBlocks

/-!
# Tables: the data of a certificate as balls

## Motivation

The data of a numerical certificate are tables: mesh points, coefficients, bounds, one number for
every index. A test reads them as balls. Where do these balls come from when the table is stored
in the build, when it is stored in parts over many modules, and when it is too large to be stored
at all?

## The idea

A test never sees a table. It sees an environment, a function from an index to a ball, and the
soundness theorem asks only that each ball encloses the real entry. So the cases differ in
that function alone.

* Stored. An entry is an integer numerator in a slot of a packed natural literal, at a fixed
  scale `2 ^ -s`. `entryBall` is its exact ball (radius zero) and `entryVal` the real number it
  stands for; `gridBall` is the general ball with a stored radius, for entries known up to an
  error bound.
* Stored in blocks. A table of many entries is not one literal: a read of one entry would
  shift the whole number. It is `blockSlot w q blocks`, entry `i % q` of the literal
  `blocks (i / q)`, where `blocks` selects one of many small literals by a tree of comparisons
  ([SlotBlocks](../Numerics/SlotBlocks.lean)). The parts of a table, one module each, are
  joined by one more selection. `pinned_hex%` and `nat_tree%` ([Shard](Shard.lean)) build both.
* Partly present. A program that reads the parts of a table from files holds a few parts at a
  time. Its lookup returns `none` for an entry that it does not hold, and `entryBall?` turns
  `none` into an invalid ball, which encloses every real number and which no comparison accepts.
  So a test that passes on a window of the table proves the statement about the whole table,
  with no proof about which entries the test reads. A condition can pass although an entry is
  absent, when it does not depend on that entry: the other side of a disjunction passes, or the
  entry is raised to the power `0`. That is sound, since the invalid ball encloses whatever the
  entry is.
* Recomputed. A generator written as expressions over a small seed gives the environment
  `fun i ↦ ball P seed (g i)`, the ball of the expression `g i` for every index `i`, and its
  enclosure is `ball_encloses` itself: nothing is defined or proved for it here. When the true
  entry is only known to lie within an error bound of the generated value, `widen` enlarges
  the ball by that bound. Storage is replaced by evaluation time.

## Main results

* `enclosesReal_gridBall` (all scales, numerators, radii): the ball of a stored center and
  radius encloses every real number within the radius of the center.
* `enclosesReal_entryBall` (all entries): `entryBall P s w v` encloses `entryVal s w v`.
* `enclosesReal_entryBall?` (all entries that may be absent): the ball of an entry that is
  absent, or present and equal to `v`, encloses `entryVal s w v`.
* `enclosesReal_widen` (all balls): if `B` encloses `y` and `|x - y| ≤ r / 2 ^ s`, then
  `widen P s r B` encloses `x`.

## Relations

`enclosesReal_entryBall` is `enclosesReal_gridBall` with radius zero, and
`enclosesReal_entryBall?` is `enclosesReal_entryBall` or `enclosesReal_of_not_ok`.
`enclosesReal_widen` is `EnclosesReal.add` with `enclosesReal_gridBall`. The environments built
here are the hypothesis `henv` of `Cond.holds_of_check` ([Cond](Cond.lean)); the elaborators of
[Shard](Shard.lean) create the literals and their selection trees, and [Run](Run.lean) reads
parts from files into partial lookups. [Seed](../Examples/Cert/Seed.lean) recomputes its
tables with `ball` and uses `widen`.

## Scope

Entries are dyadic numbers at one scale per table. A table with a different scale per entry, or
with entries in floating-point form, needs its own decoding function and enclosure lemma.
-/

@[expose] public section

namespace CAS.Cert

open CAS.Numerics CAS.Verified

/-- The ball with center `(p - n) / 2 ^ s` and radius `r / 2 ^ s` at precision `P`, valid for
`s ≤ P`. -/
def gridBall (P s p n r : ℕ) : GridBall :=
  ⟨Nat.shiftLeft p (Nat.sub P s), Nat.shiftLeft n (Nat.sub P s), Nat.shiftLeft r (Nat.sub P s),
    Nat.ble s P⟩

/-- `gridBall P s p n r` encloses every real number within `r / 2 ^ s` of `(p - n) / 2 ^ s`. -/
theorem enclosesReal_gridBall {P s p n r : ℕ} {x : ℝ}
    (hx : |x - ((p : ℝ) - n) / 2 ^ s| ≤ r / 2 ^ s) : (gridBall P s p n r).EnclosesReal P x := by
  intro hok
  have hs : s ≤ P := by simpa [gridBall] using hok
  have h2 : (0 : ℝ) < 2 ^ s := by positivity
  have hP : (2 : ℝ) ^ P = 2 ^ (P - s) * 2 ^ s := by rw [← pow_add, Nat.sub_add_cancel hs]
  have hx' : |x * 2 ^ s - ((p : ℝ) - n)| ≤ r := by
    have h3 : x * 2 ^ s - ((p : ℝ) - n) = (x - ((p : ℝ) - n) / 2 ^ s) * 2 ^ s := by
      field_simp
    rw [h3, abs_mul, abs_of_pos h2]
    calc |x - ((p : ℝ) - n) / 2 ^ s| * 2 ^ s ≤ r / 2 ^ s * 2 ^ s :=
          mul_le_mul_of_nonneg_right hx h2.le
      _ = r := div_mul_cancel₀ _ h2.ne'
  have key : x * 2 ^ P - ((gridBall P s p n r).center : ℝ) =
      (x * 2 ^ s - ((p : ℝ) - n)) * 2 ^ (P - s) := by
    simp only [gridBall, GridBall.center, Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.sub_eq]
    push_cast
    rw [hP]
    ring
  rw [key, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (P - s))]
  have : ((gridBall P s p n r).e : ℝ) = r * 2 ^ (P - s) := by
    simp only [gridBall, Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.sub_eq]
    push_cast
    ring
  rw [this]
  exact mul_le_mul_of_nonneg_right hx' (by positivity)

/-- The real number that the entry `v` stands for: a signed integer stored with the bias of a
slot of width `w`, at the scale `2 ^ -s`, that is `(v - slotBias w) / 2 ^ s`. -/
noncomputable def entryVal (s w v : ℕ) : ℝ := ((v : ℝ) - slotBias w) / 2 ^ s

/-- The exact ball of the entry `v`. -/
def entryBall (P s w v : ℕ) : GridBall := gridBall P s v (slotBias w) 0

/-- `entryBall P s w v` encloses the stored real number `entryVal s w v`. -/
theorem enclosesReal_entryBall (P s w v : ℕ) :
    (entryBall P s w v).EnclosesReal P (entryVal s w v) :=
  enclosesReal_gridBall (by simp [entryVal])

/-- The ball of an entry that may be absent: the exact ball of `v` for `some v`, and an invalid
ball, which no comparison accepts, for `none`. -/
def entryBall? (P s w : ℕ) : Option ℕ → GridBall
  | none => GridBall.invalid
  | some v => entryBall P s w v

/-- **Absent entries are harmless.** If the entry `o` is absent, or present and equal to `v`,
then `entryBall? P s w o` encloses `entryVal s w v`. So a lookup that holds only some entries of
a table gives balls that enclose the whole table. -/
theorem enclosesReal_entryBall? {P s w : ℕ} {o : Option ℕ} {v : ℕ} (h : ∀ u, o = some u → v = u) :
    (entryBall? P s w o).EnclosesReal P (entryVal s w v) := by
  cases o with
  | none => exact GridBall.enclosesReal_of_not_ok rfl _
  | some u => rw [h u rfl]; exact enclosesReal_entryBall P s w u

/-- A lookup that has every entry, as a lookup whose entries may be absent. -/
def total (look : ℕ → ℕ → ℕ) (t i : ℕ) : Option ℕ := some (look t i)

/-- An entry of `total look` is the entry of `look`. -/
theorem total_eq_some {look : ℕ → ℕ → ℕ} {t i v : ℕ} (h : total look t i = some v) :
    look t i = v :=
  Option.some.inj h

/-! ### Tables known up to an error bound -/

/-- The ball `B` with its radius enlarged by `r / 2 ^ s`. -/
def widen (P s r : ℕ) (B : GridBall) : GridBall := GridBall.add B (gridBall P s 0 0 r)

/-- **A generator with an error bound.** If `B` encloses `y` and `|x - y| ≤ r / 2 ^ s`, then
`widen P s r B` encloses `x`. With `B` the ball of a generator, `x` is a true entry that the
generator approximates within a proved bound. -/
theorem enclosesReal_widen {P s r : ℕ} {B : GridBall} {x y : ℝ} (hB : B.EnclosesReal P y)
    (h : |x - y| ≤ r / 2 ^ s) : (widen P s r B).EnclosesReal P x := by
  have hd : (gridBall P s 0 0 r).EnclosesReal P (x - y) :=
    enclosesReal_gridBall (by simpa using h)
  have hsum := hB.add hd
  rw [add_sub_cancel] at hsum
  exact hsum

end CAS.Cert

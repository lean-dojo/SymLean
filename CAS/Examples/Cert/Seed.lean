/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Examples.Cert.MeshSpec
public meta import CAS.Examples.Cert.MeshSpec
public import CAS.Cert.Shard
public meta import CAS.Cert.Shard

/-!
# Recompute instead of store: the tables of a mesh from a seed

## Motivation

The tables of a fine mesh can be too large for any build: one number per coefficient and cell.
Often they are not independent data. They are the fine form of a small description, such as
the coefficients of a profile on a coarse grid with their error bounds. Can the check of
[MeshSpec](MeshSpec.lean) run on tables that exist nowhere, with the seed as its only data?

## The idea

A test reads its tables through an environment of balls, and the soundness theorem asks only
that every ball encloses the real entry. So the environment may compute its balls. Here the
seed is four coefficients `a 0, …, a 3` of a cubic, each known within `2 ^ -30` of a stored
center. The mesh points are `k / 2 ^ m`. The four coefficients of cell `k` are the Taylor
coefficients of the cubic at the mesh point, written as expressions in the seed (`taylor`) and
evaluated on balls each time the test reads them; their enclosure is the soundness of the
evaluator itself. The bound is the constant `1 / 2`. The condition is `MeshSpec.cellCond`,
the same term as for stored tables.

Storage has become time: the seed has four numbers, whatever the number of cells, and each
coefficient costs a few operations on balls each time it is read.

The second statement is about a table that no program can compute: at a mesh point `k / 256`,
any real number within `2 ^ -20` of a seed cubic, such as the value of a function that the
cubic approximates. Its ball is the recomputed value of the cubic, widened by the error bound
(`widen`).

## Main results

* `benv_encloses` (all seeds within the error bounds, all mesh sizes): the recomputed balls
  enclose the recomputed real tables.
* `cubic_le` (a family: every cubic whose four coefficients lie within `2 ^ -30` of the stored
  centers): `a 0 + a 1 t + a 2 t ^ 2 + a 3 t ^ 3 ≤ 1 / 2` for every `t` in `[0, 1]`. The proof
  is the test of 256 cells, evaluated by the kernel in four declarations.
* `nonempty_cert` (one example): the checker of `MeshSpec` accepts the recomputed tables and
  gives a certificate `MeshSpec.CellCert 256`, the type that stored tables give.
* `value_le_of_near` (a family: every seed, every mesh point `k / 256` with `k ≤ 256` and
  every real number within `2 ^ -20` of the cubic there): the number is at most `1 / 2`.
* `value_le` (a family: every function within `2 ^ -20` of such a cubic):
  `f (k / 256) ≤ 1 / 2` for every `k ≤ 256`.

## Relations

`benv_encloses` is `ball_encloses` ([Ball](../../Cert/Ball.lean)). `cubic_le` uses
`MeshSpec.cell_bound` with the environment `benv`, `exists_cell` for the mesh, and the identity
between a cubic and its Taylor polynomial. `value_le_of_near` uses `enclosesReal_widen`
([Table](../../Cert/Table.lean)) and `Cond.holds_of_run`, and `value_le` is its case at the
values of a function. [Mesh](Mesh.lean) is the same condition on stored tables. The range
theorems `cells` and `values` are stated by `cert_shard` ([Shard](../../Cert/Shard.lean)), so
compiled code evaluates the same module under `cega.nativeCertificates`, and
`scripts/CertStubs.lean` cuts a larger mesh into modules from a manifest without tables.

## Scope

One family of seeds, a cubic on `[0, 1]`. A seed of a real proof (a spline on a coarse grid, a
truncated expansion) needs its own generator, written as expressions, and the proof of its
error bound.
-/

@[expose] public section

namespace CAS.Examples.Cert.Seed

open CAS.Cert CAS.Numerics CAS.Verified MeshSpec

/-! ### The seed -/

/-- The numerator of the center of seed coefficient `j` at the scale `2 ^ -40`, as a positive
and a negative part: the centers are `3/8`, `-5/4`, `7/2`, `-9/4`. -/
def center : ℕ → ℕ × ℕ
  | 0 => (Nat.shiftLeft 3 37, 0)
  | 1 => (0, Nat.shiftLeft 5 38)
  | 2 => (Nat.shiftLeft 7 39, 0)
  | _ => (0, Nat.shiftLeft 9 38)

/-- The ball of seed coefficient `j < 4`: its center, with the radius `2 ^ -30`. There is no
coefficient `j ≥ 4`, and its ball is invalid. -/
def seedBall (j : ℕ) : GridBall :=
  Bool.rec GridBall.invalid (gridBall 96 40 (center j).1 (center j).2 (Nat.shiftLeft 1 10))
    (Nat.blt j 4)

/-- The real center of seed coefficient `j`. -/
noncomputable def centerVal (j : ℕ) : ℝ := (((center j).1 : ℝ) - (center j).2) / 2 ^ 40

/-- A seed: four real coefficients `a 0, …, a 3`, each within `2 ^ -30` of its center. The
values `a j` for `j ≥ 4` are not constrained and not used. -/
def IsSeed (a : ℕ → ℝ) : Prop := ∀ j, j < 4 → |a j - centerVal j| ≤ 1 / 2 ^ 30

/-- The centers are a seed, so the family of seeds is not empty. -/
theorem isSeed_centerVal : IsSeed centerVal := fun j _ ↦ by simp

/-- The balls of the seed enclose every seed. -/
theorem seedBall_encloses {a : ℕ → ℝ} (ha : IsSeed a) (j : ℕ) :
    (seedBall j).EnclosesReal 96 (a j) := by
  unfold seedBall
  cases hj : Nat.blt j 4
  · exact GridBall.enclosesReal_of_not_ok rfl _
  · refine enclosesReal_gridBall ((ha j (by simpa using hj)).trans (le_of_eq ?_))
    rw [show Nat.shiftLeft 1 10 = 1024 from rfl]
    norm_num

/-! ### The generator -/

/-- The variables of the generator: seed coefficient `j`, and the mesh point of the cell. -/
inductive Var where
  /-- Seed coefficient `j`. -/
  | seed (j : ℕ)
  /-- The mesh point of the cell. -/
  | point

/-- Taylor coefficient `j` of the cubic at the mesh point, as an expression in the seed. -/
def taylor : ℕ → Expr Var
  | 0 => .add (.var (.seed 0)) (.mul (.var .point) (.add (.var (.seed 1)) (.mul (.var .point)
      (.add (.var (.seed 2)) (.mul (.var .point) (.var (.seed 3)))))))
  | 1 => .add (.var (.seed 1)) (.mul (.var .point) (.add (.mul (.nat 2) (.var (.seed 2)))
      (.mul (.mul (.nat 3) (.var (.seed 3))) (.var .point))))
  | 2 => .add (.var (.seed 2)) (.mul (.mul (.nat 3) (.var (.seed 3))) (.var .point))
  | 3 => .var (.seed 3)
  | _ => .nat 0

/-- Mesh point `k` of `2 ^ m` cells of `[0, 1]`, as an exact ball. -/
def meshBall (m k : ℕ) : GridBall := gridBall 96 m k 0 0

/-- The mesh ball encloses the mesh point `k / 2 ^ m`. -/
theorem meshBall_encloses (m k : ℕ) : (meshBall m k).EnclosesReal 96 ((k : ℝ) / 2 ^ m) :=
  enclosesReal_gridBall (by simp)

/-- The balls of the variables of the generator at cell `k`. -/
def genBenv (m k : ℕ) : Var → GridBall
  | .seed j => seedBall j
  | .point => meshBall m k

/-- The real variables of the generator at cell `k`, for the seed `a`. -/
noncomputable def genEnv (m : ℕ) (a : ℕ → ℝ) (k : ℕ) : Var → ℝ
  | .seed j => a j
  | .point => (k : ℝ) / 2 ^ m

/-- The balls of the generator enclose its real variables. -/
theorem genBenv_encloses (m : ℕ) {a : ℕ → ℝ} (ha : IsSeed a) (k : ℕ) (v : Var) :
    (genBenv m k v).EnclosesReal 96 (genEnv m a k v) := by
  cases v with
  | seed j => exact seedBall_encloses ha j
  | point => exact meshBall_encloses m k

/-! ### The recomputed tables and their test -/

/-- The recomputed tables as balls: the mesh points `k / 2 ^ m`, the Taylor coefficients of the
cells, recomputed from the seed, and the bound `1 / 2`. -/
def benv (m : ℕ) : Ix → GridBall
  | .mesh k => meshBall m k
  | .coef k j => ball 96 (genBenv m k) (taylor j)
  | .bound _ => gridBall 96 1 1 0 0

/-- The recomputed tables as real numbers, for the seed `a`. -/
noncomputable def env (m : ℕ) (a : ℕ → ℝ) : Ix → ℝ
  | .mesh k => (k : ℝ) / 2 ^ m
  | .coef k j => (taylor j).eval (genEnv m a k)
  | .bound _ => 1 / 2

/-- **The recomputed balls enclose the recomputed tables**, for every seed and every mesh
size. The coefficients are enclosed by the soundness of the evaluator. -/
theorem benv_encloses (m : ℕ) {a : ℕ → ℝ} (ha : IsSeed a) (i : Ix) :
    (benv m i).EnclosesReal 96 (env m a i) := by
  cases i with
  | mesh k => exact meshBall_encloses m k
  | coef k j => exact ball_encloses (genBenv_encloses m ha k) (taylor j)
  | bound k => exact enclosesReal_gridBall (by norm_num [env])

/-- The test of cell `k` of `2 ^ m` cells: the condition of `MeshSpec` on the recomputed
tables. -/
def test (m k : ℕ) : Bool := (cellCond k).run 96 (benv m)

/-- The tests of the 256 cells pass. -/
cert_shard cells : (test 8) (below := 256) (start := 0) (count := 256) (batch := 64)
  (unfolding := [test, cellCond, meshAt, coefAt, boundAt, «local», benv, genBenv, taylor,
    seedBall, center, meshBall, gridBall])

/-- **A bound for a family of cubics from recomputed tables.** For every seed, that is for all
real coefficients `a 0, …, a 3` within `2 ^ -30` of `3/8`, `-5/4`, `7/2`, `-9/4`, and every real
`t` in `[0, 1]`: `a 0 + a 1 t + a 2 t ^ 2 + a 3 t ^ 3 ≤ 1 / 2`.

No table is stored. The 256 cells of the mesh are tested with coefficients that are recomputed
from the seed each time they are read, and the Taylor polynomial of a cubic at a mesh point is
the cubic. -/
theorem cubic_le {a : ℕ → ℝ} (ha : IsSeed a) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    a 0 + a 1 * t + a 2 * t ^ 2 + a 3 * t ^ 3 ≤ 1 / 2 := by
  -- The cell of `t`.
  obtain ⟨k, hk, hlo, hhi⟩ := exists_cell (t := fun k ↦ (k : ℝ) / 2 ^ 8) (n := 256) (by norm_num)
    (by simpa using h0) (by norm_num; exact h1)
  -- The statement of that cell, for the real tables of the seed.
  have h := cell_bound (benv_encloses 8 ha) (forall_of_rangeAll (n := 256) cells ⟨k, hk⟩) t hlo hhi
  -- The Taylor polynomial at the mesh point is the cubic.
  have e : a 0 + a 1 * t + a 2 * t ^ 2 + a 3 * t ^ 3 =
      env 8 a (.coef k 0) + (t - env 8 a (.mesh k)) * (env 8 a (.coef k 1) +
        (t - env 8 a (.mesh k)) * (env 8 a (.coef k 2) +
          (t - env 8 a (.mesh k)) * env 8 a (.coef k 3))) := by
    simp only [env, taylor, genEnv, Expr.eval, Nat.cast_ofNat]
    ring
  rw [e]
  exact h

/-- The checker of `MeshSpec` accepts the recomputed tables: a certificate for 256 cells, of the
type that stored tables give. The type is inhabited by zero tables as well
([MeshSpec](MeshSpec.lean)); the statement of interest is `cubic_le`. -/
theorem nonempty_cert : Nonempty (CellCert 256) :=
  (checker 96 256 (benv 8)).sound
    (checker_run fun k hk ↦ forall_of_rangeAll (n := 256) cells ⟨k, hk⟩)

/-! ### A table known up to an error bound -/

/-- The ball of the value at mesh point `k` of a function within `2 ^ -20` of a seed cubic: the
recomputed value of the cubic, widened by the error bound. -/
def valueBall (k : ℕ) : GridBall := widen 96 20 1 (ball 96 (genBenv 8 k) (taylor 0))

/-- The test at mesh point `k`: the value is at most `1 / 2`. -/
def valueTest (k : ℕ) : Bool :=
  (Cond.le (Cond.dat k) (.rat 1 2) : Cond ℕ).run 96 valueBall

/-- The tests of the 257 mesh points pass. -/
cert_shard values : valueTest (below := 257) (start := 0) (count := 257) (batch := 64)
  (unfolding := [valueTest, valueBall, genBenv, taylor, seedBall, center, meshBall, gridBall])

/-- **A table known up to an error bound.** Let `a` be a seed, `k ≤ 256` and `y` any real
number within `2 ^ -20` of the value `a 0 + a 1 x + a 2 x ^ 2 + a 3 x ^ 3` of the cubic at the
mesh point `x = k / 256`. Then `y ≤ 1 / 2`. The number `y` is not computed: its ball is the
recomputed value of the cubic, widened by the error bound. Nothing is assumed about the other
mesh points, where the test reads the cubic itself. -/
theorem value_le_of_near {a : ℕ → ℝ} (ha : IsSeed a) {k : ℕ} (hk : k ≤ 256) {y : ℝ}
    (hy : |y - (a 0 + a 1 * (k / 2 ^ 8) + a 2 * (k / 2 ^ 8) ^ 2 + a 3 * (k / 2 ^ 8) ^ 3)| ≤
      1 / 2 ^ 20) : y ≤ 1 / 2 := by
  -- The value of the cubic at mesh point `j`.
  have e : ∀ j : ℕ, (taylor 0).eval (genEnv 8 a j) = a 0 + a 1 * ((j : ℝ) / 2 ^ 8) +
      a 2 * ((j : ℝ) / 2 ^ 8) ^ 2 + a 3 * ((j : ℝ) / 2 ^ 8) ^ 3 := fun j ↦ by
    simp only [taylor, genEnv, Expr.eval]
    ring
  -- The table: `y` at the mesh point `k`, the cubic at the others. The widened balls enclose it.
  have henv : ∀ j, (valueBall j).EnclosesReal 96
      (if j = k then y else (taylor 0).eval (genEnv 8 a j)) := fun j ↦
    enclosesReal_widen (ball_encloses (genBenv_encloses 8 ha j) (taylor 0)) (by
      split
      · rename_i hjk
        rw [hjk, e]
        simpa using hy
      · simp)
  have h := Cond.holds_of_run henv _ (fun _ ↦ 0)
    (forall_of_rangeAll (n := 257) values ⟨k, by omega⟩)
  simpa [Cond.holds] using h

/-- **A function known up to an error bound.** Let `a` be a seed and `f` any real function with
`|f x - (a 0 + a 1 x + a 2 x ^ 2 + a 3 x ^ 3)| ≤ 2 ^ -20` for every `x`. Then
`f (k / 256) ≤ 1 / 2` at each of the 257 mesh points. This is `value_le_of_near` at the values
of `f`. -/
theorem value_le {a : ℕ → ℝ} (ha : IsSeed a) {f : ℝ → ℝ}
    (hf : ∀ x, |f x - (a 0 + a 1 * x + a 2 * x ^ 2 + a 3 * x ^ 3)| ≤ 1 / 2 ^ 20) {k : ℕ}
    (hk : k ≤ 256) : f (k / 2 ^ 8) ≤ 1 / 2 :=
  value_le_of_near ha hk (hf _)

end CAS.Examples.Cert.Seed

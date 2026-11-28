/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Cert.Run

/-!
# A table inequality on a mesh: the condition and its checker

## Motivation

A typical hypothesis of a computer-assisted proof in analysis says that a function given by
coefficients stays below a bound on every cell of a mesh, as the cell conditions of
`NumericalBounds` in BlowupZoo's `Boussinesq/BoundaryBlowup` do. How is such a hypothesis
written once, so that the same text is checked whether the tables are stored in one module, cut
into parts over many modules, recomputed from a seed, or read from files by a program?

## The idea

There are three tables, indexed by `Ix`: the mesh points `mesh k`, four coefficients `coef k j`
for every cell `k`, and one bound `bound k` for every cell. The condition of cell `k` says that
for every real `x` of the cell `[mesh k, mesh (k + 1)]` the cubic
`coef k 0 + coef k 1 h + coef k 2 h ^ 2 + coef k 3 h ^ 3` in `h = x - mesh k` is at most
`bound k` (`cellCond`). It is one term of the language of [Cond](../../Cert/Cond.lean) and
does not say where the tables come from: they enter through an environment of balls
`Ix → GridBall` that encloses real tables `Ix → ℝ`.

For stored tables the environment is `stored look?`: the entries are 64-bit integers at the
scale `2 ^ -40`, read through a lookup `look? : ℕ → ℕ → Option ℕ` (table, then index) that may
hold only a part of the tables. `test look? k` is the test of cell `k` at 96 bits.

## Main results

* `holds_cellCond` (all real tables, all cells): the condition of cell `k` holds exactly when
  the cubic of the cell is at most its bound at every real point of the cell.
* `cell_bound` (all environments, all cells, all precisions): if the balls enclose the real
  tables and the test of cell `k` passes, then the cubic of the cell is at most its bound at
  every real point of the cell.
* `CellCert`, `nonempty_cert` (all real tables): a type of certificates stated over the real
  numbers, and a certificate from the real tables once every cell passed its test on some
  balls that enclose them.
* `checker` (a construction, for all balls): a `Check (Nonempty (CellCert n))` whose test is
  the test of the `n` cells; `storedChecker` is the case of stored tables.
* `cells_of_shardOk` (all manifests `m` with `0 < m.shard`, all byte strings): if the shard
  tests pass on given byte strings, their tables satisfy the condition of each of the `m.count`
  cells.
* `cells_of_run` (all manifests): a run of `test` over the files of a manifest `m` gives byte
  strings with the lengths and digests of `m` whose tables satisfy the condition of each of the
  `m.count` cells. This is the statement of a run with content.
* `nonempty_of_run` (all manifests): such a run gives `Nonempty (CellCert m.count)`. This is the
  form `∀ input, run input = success → Nonempty CertType`, with the run as a hypothesis.

## Relations

`cell_bound` is `Cond.holds_of_run` read through `holds_cellCond`. `nonempty_cert` is
`Cond.holds_of_run` at every cell with `nonempty_of_holds`, and `checker` is `nonempty_cert`
with the centers of the balls as real tables (`enclosesReal_center`). `cells_of_shardOk` is
`Cond.holds_of_run` on the window of each shard, from `Run.test_of_shardOk`, and
`Mesh.run_cubic_le_bound` uses it on the byte strings of an instance. `cells_of_run` is
`Cond.holds_of_run` on the window of each shard, from `Run.Ok.exists_texts`
([Run](../../Cert/Run.lean)) and `enclosesReal_entryBall?` ([Table](../../Cert/Table.lean)),
and `nonempty_of_run` is `nonempty_of_holds` at the tables of `cells_of_run`.
[Mesh](Mesh.lean) proves the tests of stored tables in two parts and meets the hypothesis of
`cells_of_run`; [Seed](Seed.lean) checks the same condition on tables that are recomputed.

## Scope

This is one example of a condition, a cubic on an interval; the cell conditions of a real
proof are written in the same language with their own expressions. The certificate type
`CellCert n` shows the shape of the pattern and nothing more: its conditions are upper bounds,
so zero tables inhabit it, and `Nonempty (CellCert n)` is true without any computation. The
certificate type of a real theorem contains conditions that pin its data. What a computation
proves here about given tables is `cell_bound`, about the files of a run `cells_of_run`, and
about a family of functions `Seed.cubic_le`.
-/

@[expose] public section

namespace CAS.Examples.Cert.MeshSpec

open CAS.Cert CAS.Numerics CAS.Verified

/-- The entries of the three tables: mesh point `k`, coefficient `j` of cell `k`, and the bound
of cell `k`. -/
inductive Ix where
  /-- Mesh point `k`. -/
  | mesh (k : ℕ)
  /-- Coefficient `j` of cell `k`. -/
  | coef (k j : ℕ)
  /-- The bound of cell `k`. -/
  | bound (k : ℕ)

/-- Mesh point `k`, as an expression. -/
def meshAt (k : ℕ) : Expr (Ix ⊕ ℕ) := Cond.dat (.mesh k)

/-- Coefficient `j` of cell `k`, as an expression. -/
def coefAt (k j : ℕ) : Expr (Ix ⊕ ℕ) := Cond.dat (.coef k j)

/-- The bound of cell `k`, as an expression. -/
def boundAt (k : ℕ) : Expr (Ix ⊕ ℕ) := Cond.dat (.bound k)

/-- The local variable `x - mesh k` of cell `k`. -/
def «local» (k : ℕ) : Expr (Ix ⊕ ℕ) := .sub (Cond.cell 0) (meshAt k)

/-- The condition of cell `k`: at every `x` of `[mesh k, mesh (k + 1)]` the cubic of the cell,
in Horner form, is at most the bound of the cell. The test may cut the cell in two once. -/
def cellCond (k : ℕ) : Cond Ix :=
  .onIcc (meshAt k) (meshAt (Nat.add k 1)) 1
    (.le (.add (coefAt k 0) (.mul («local» k) (.add (coefAt k 1) (.mul («local» k)
      (.add (coefAt k 2) (.mul («local» k) (coefAt k 3))))))) (boundAt k))

/-- **What the condition of a cell says.** For real tables `env`, the condition of cell `k`
holds exactly when the cubic of the cell is at most its bound at every real `x` between the mesh
points `mesh k` and `mesh (k + 1)`. The condition binds its cell variable, so the values `σ` of
the free cell variables do not matter. The kernel checks here that the term `cellCond k` of the
language is the inequality it stands for. -/
theorem holds_cellCond {env : Ix → ℝ} {k : ℕ} {σ : ℕ → ℝ} :
    (cellCond k).holds env σ ↔ ∀ x : ℝ, env (.mesh k) ≤ x → x ≤ env (.mesh (k + 1)) →
      env (.coef k 0) + (x - env (.mesh k)) * (env (.coef k 1) +
        (x - env (.mesh k)) * (env (.coef k 2) + (x - env (.mesh k)) * env (.coef k 3))) ≤
        env (.bound k) := by
  simp [cellCond, Cond.holds, meshAt, coefAt, boundAt, «local»]

/-- **The statement of one cell.** If the balls `benv` enclose the real tables `env` and the
test of cell `k` passes on `benv`, then for every real `x` between the mesh points `mesh k` and
`mesh (k + 1)` the cubic of the cell is at most its bound. -/
theorem cell_bound {P : ℕ} {benv : Ix → GridBall} {env : Ix → ℝ}
    (henv : ∀ i, (benv i).EnclosesReal P (env i)) {k : ℕ}
    (h : (cellCond k).run P benv = true) (x : ℝ) (hlo : env (.mesh k) ≤ x)
    (hhi : x ≤ env (.mesh (k + 1))) :
    env (.coef k 0) + (x - env (.mesh k)) * (env (.coef k 1) +
      (x - env (.mesh k)) * (env (.coef k 2) + (x - env (.mesh k)) * env (.coef k 3))) ≤
      env (.bound k) :=
  holds_cellCond.mp (Cond.holds_of_run henv (cellCond k) (fun _ ↦ 0) h) x hlo hhi

/-- A certificate for `n` cells, stated over the real numbers: mesh points, coefficients and
bounds such that the cubic of every cell is at most its bound on the cell. -/
structure CellCert (n : ℕ) where
  /-- The mesh points. -/
  x : ℕ → ℝ
  /-- The coefficients of the cells. -/
  c : ℕ → ℕ → ℝ
  /-- The bounds of the cells. -/
  b : ℕ → ℝ
  /-- On every cell the cubic is at most the bound. -/
  le : ∀ k, k < n → ∀ t : ℝ, x k ≤ t → t ≤ x (k + 1) →
    c k 0 + (t - x k) * (c k 1 + (t - x k) * (c k 2 + (t - x k) * c k 3)) ≤ b k

/-- Real tables `env` whose `n` cells satisfy their conditions are a certificate. -/
theorem nonempty_of_holds {n : ℕ} {env : Ix → ℝ}
    (h : ∀ k, k < n → (cellCond k).holds env fun _ ↦ 0) : Nonempty (CellCert n) :=
  ⟨{ x := fun k ↦ env (.mesh k)
     c := fun k j ↦ env (.coef k j)
     b := fun k ↦ env (.bound k)
     le := fun k hk ↦ holds_cellCond.mp (h k hk) }⟩

/-- **A certificate from the tests of the cells.** If each of the `n` cells passed its test on
some balls that enclose the real tables `env`, then `env` is a certificate. The balls may differ
from cell to cell, as they do when each shard of a run holds its own part of the tables. -/
theorem nonempty_cert {P n : ℕ} {env : Ix → ℝ}
    (h : ∀ k, k < n → ∃ benv : Ix → GridBall,
      (∀ i, (benv i).EnclosesReal P (env i)) ∧ (cellCond k).run P benv = true) :
    Nonempty (CellCert n) :=
  nonempty_of_holds fun k hk ↦
    let ⟨_, henv, hrun⟩ := h k hk
    Cond.holds_of_run henv (cellCond k) _ hrun

/-- The checker for tables given as balls `benv`: the tests of the `n` cells; if they pass, the
centers of the balls are a certificate. Its only input is the balls, so the test is a program
of data alone. -/
def checker (P n : ℕ) (benv : Ix → GridBall) : Check (Nonempty (CellCert n)) :=
  ⟨natAll n fun k ↦ (cellCond k).run P benv, fun h ↦
    nonempty_cert fun _ hk ↦
      ⟨benv, fun i ↦ GridBall.enclosesReal_center P (benv i), natAll_spec h hk⟩⟩

/-- The checker accepts tables whose `n` tests pass. -/
theorem checker_run {P n : ℕ} {benv : Ix → GridBall}
    (h : ∀ k, k < n → (cellCond k).run P benv = true) : (checker P n benv).run = true :=
  natAll_eq_true_iff.mpr h

/-! ### Stored tables -/

/-- The balls of stored tables: the mesh is table `0`, the coefficients are table `1` with
coefficient `j` of cell `k` at index `4 k + j`, the bounds are table `2`. An entry is a 64-bit
integer at the scale `2 ^ -40`, at 96 bits; an entry that the lookup does not hold gives an
invalid ball. -/
def stored (look? : ℕ → ℕ → Option ℕ) : Ix → GridBall
  | .mesh k => entryBall? 96 40 64 (look? 0 k)
  | .coef k j => entryBall? 96 40 64 (look? 1 (Nat.add (Nat.mul 4 k) j))
  | .bound k => entryBall? 96 40 64 (look? 2 k)

/-- The real tables that the stored integers of `look` stand for. -/
noncomputable def storedVal (look : ℕ → ℕ → ℕ) : Ix → ℝ
  | .mesh k => entryVal 40 64 (look 0 k)
  | .coef k j => entryVal 40 64 (look 1 (4 * k + j))
  | .bound k => entryVal 40 64 (look 2 k)

/-- The balls of a partial lookup enclose the real tables of every total lookup that has its
entries. -/
theorem stored_encloses {look? : ℕ → ℕ → Option ℕ} {look : ℕ → ℕ → ℕ}
    (h : ∀ t i v, look? t i = some v → look t i = v) (i : Ix) :
    (stored look? i).EnclosesReal 96 (storedVal look i) := by
  cases i <;> exact enclosesReal_entryBall? (h _ _)

/-- The test of cell `k` at 96 bits, for stored tables read through `look?`. -/
def test (look? : ℕ → ℕ → Option ℕ) (k : ℕ) : Bool := (cellCond k).run 96 (stored look?)

/-- The checker for stored tables `look`: the tests of the `n` cells at 96 bits. -/
def storedChecker (n : ℕ) (look : ℕ → ℕ → ℕ) : Check (Nonempty (CellCert n)) :=
  checker 96 n (stored (total look))

/-- The checker accepts stored tables whose `n` tests pass. -/
theorem storedChecker_run {n : ℕ} {look : ℕ → ℕ → ℕ}
    (h : ∀ k, k < n → test (total look) k = true) : (storedChecker n look).run = true :=
  checker_run h

/-- **The statement of the shard tests of given byte strings.** For every manifest `m` with
`0 < m.shard` and all byte strings `texts`: if the test of every shard passes on `texts`, then
the real tables that `texts` stand for satisfy the condition of each of the `m.count` cells.
Each cell was tested through the window of its shard, whose balls enclose the tables of all
byte strings (`stored_encloses`). -/
theorem cells_of_shardOk {m : Run.Manifest} {texts : ℕ → ℕ → ByteArray} (hs : 0 < m.shard)
    (hall : ∀ j, j * m.shard < m.count → Run.shardOk m test texts j = true) {k : ℕ}
    (hk : k < m.count) (σ : ℕ → ℝ) : (cellCond k).holds (storedVal (Run.look m texts)) σ :=
  Cond.holds_of_run (stored_encloses fun _ _ _ ↦ Run.look_of_windowLook) (cellCond k) σ
    (Run.test_of_shardOk hs hall hk)

/-- **The statement of a run over files.** For every manifest `m`: if a run of `test` over
files with the lengths and digests of `m` passed (`Run.Ok m test`), then there are byte strings
with these lengths and digests (`Run.Matches m texts`) such that the real tables which they
stand for satisfy the condition of each of the `m.count` cells: by `holds_cellCond`, the cubic
of every cell is at most its bound on the cell.

This is what a run establishes about the data. The byte strings are those of the run; each cell
was tested through the window of its shard, whose balls enclose the tables of all byte strings
(`stored_encloses`). The statement is false for a manifest whose digests no such byte strings
have, so it is not true without the run. -/
theorem cells_of_run {m : Run.Manifest} (h : Run.Ok m test) :
    ∃ texts : ℕ → ℕ → ByteArray, Run.Matches m texts ∧
      ∀ k, k < m.count → ∀ σ, (cellCond k).holds (storedVal (Run.look m texts)) σ := by
  obtain ⟨texts, hm, hlook⟩ := h.exists_texts
  exact ⟨texts, hm, fun k hk σ ↦
    let ⟨_, hagree, hrun⟩ := hlook k hk
    Cond.holds_of_run (stored_encloses hagree) (cellCond k) σ hrun⟩

/-- **A certificate from a run over files.** For every manifest `m`: if a run of `test` over
files with the lengths and digests of `m` passed (`Run.Ok m test`), then there is a certificate
for `m.count` cells. Its tables are the real numbers that the byte strings of `cells_of_run`
stand for; the statement keeps only `m.count` of the manifest. -/
theorem nonempty_of_run {m : Run.Manifest} (h : Run.Ok m test) : Nonempty (CellCert m.count) :=
  let ⟨_, _, hcells⟩ := cells_of_run h
  nonempty_of_holds fun k hk ↦ hcells k hk _

end CAS.Examples.Cert.MeshSpec

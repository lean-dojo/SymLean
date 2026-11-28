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
import Mathlib.Tactic.IntervalCases

/-!
# A table inequality on a stored mesh: invented data in two parts

## Motivation

[MeshSpec](MeshSpec.lean) writes the condition "the cubic of each cell is at most the bound of
the cell" once. What does a build give for a concrete data set stored in parts, what does its
statement mention, and can the hypothesis of a run over files be met?

## The idea

The data are three tables for 8 cells, in parts of 4 cells: seven texts, each pinned by its
length and SHA-256 digest and stored as literals of four entries (`pinned_hex%`). The parts of
a table are joined by a selection tree (`nat_tree%`), and `look t i` is entry `i` of table `t`.
Two ranges of 4 cells are tested (`cert_shard`) and `cert_aggregate` joins them. The theorem is
about the real numbers that the stored integers stand for and does not mention balls, parts or
ranges.

Here the texts are string literals and everything is in one module, since the library embeds no
data file. For data in files, `scripts/CertStubs.lean` writes one module per part, one per
range and one for the join from a manifest, and Lake builds them in parallel;
`tests/cert/run.sh` does this for data written by `scripts/cert_synthetic.py`, which also wrote
the seven texts below.

The last section meets the hypothesis of `MeshSpec.cells_of_run`: a manifest of seven byte
strings in the format of a run, which hold the thirteen entries of the first two cells of the
stored tables with one cell per shard, and a proof of `Run.Ok` in which the kernel evaluates
the tests of both shards through their windows.

## Main results

* `cubic_le_bound` (one example: the 8 cells of the invented data): at every real point of
  every cell the cubic of the cell is at most the bound of the cell.
* `nonempty_cert` (the same example): a certificate of the type `MeshSpec.CellCert 8`, from the
  checker `MeshSpec.storedChecker` and the passing tests.
* `run_look` (one example: seven byte strings): the entries that a run reads from the texts
  of `runManifest` are the entries of the first two cells of the stored tables.
* `run_ok` (the same example): `Run.Ok runManifest MeshSpec.test`, proved by the kernel;
  `nonempty_of_tiny_run` is the certificate that `MeshSpec.nonempty_of_run` gives from it.
* `run_cubic_le_bound` (the same example): the inequality of `cubic_le_bound` on the cells 0
  and 1, proved from the tests of the run and `run_look`.

## Relations

`cubic_le_bound` is `MeshSpec.cell_bound` at the tests of `all`, which `cert_aggregate` joined
from `shard0` and `shard1`; each shard is `rangeAll_of_natAll`.
`nonempty_cert` is `Check.nonempty_of_run`. `run_ok` is `Run.ok_of_windows`
([Run](../../Cert/Run.lean)) with the tests `run_shards` of the two shards, and
`run_cubic_le_bound` is `MeshSpec.cells_of_shardOk` at these tests, read through `run_look`
and `MeshSpec.holds_cellCond`: the kernel checks that the run route and the build route state
the same inequality.

## Scope

The data are invented and small. The pins of the byte strings of `runManifest` are given by the
digest function itself (`Run.Pin.of`), because the kernel does not evaluate SHA-256, so the
instance shows that the hypothesis of a run can be met and does not compare a digest.
`nonempty_cert` and `nonempty_of_tiny_run` conclude `Nonempty (CellCert n)`, which zero tables
inhabit ([MeshSpec](MeshSpec.lean)); the statement about the stored numbers is
`cubic_le_bound`.
-/

@[expose] public section

namespace CAS.Examples.Cert.Mesh

open CAS.Cert CAS.Numerics MeshSpec

/-! ### The tables, in parts -/

/-- Part 0 of the mesh: 4 points, in one block. -/
def mesh0 : ℕ → ℕ :=
  pinned_hex% 64 4 4 68 "512e16745f56e94a4cff73e81582b4c8cf79242f5b2756bdab65e14b98d30ecd"
    "0000000000000000\n0000002700000000\n0000004c00000000\n0000006f00000000\n"

/-- Part 1 of the mesh: 4 points. -/
def mesh1 : ℕ → ℕ :=
  pinned_hex% 64 4 4 68 "0fcd9ee4074ce579385752d887e7ae85c76e1324deb3f88b6233bd739071c8e8"
    "0000009000000000\n000000af00000000\n000000cc00000000\n000000e700000000\n"

/-- Part 2 of the mesh: the last point. -/
def mesh2 : ℕ → ℕ :=
  pinned_hex% 64 4 1 17 "12ee7318138f3116c9843fad669f5d73822e6bbf6154b906ea15cb9b3f89ad8c"
    "0000010000000000\n"

/-- Part 0 of the coefficients: 4 cells, in four blocks. -/
def coef0 : ℕ → ℕ :=
  pinned_hex% 64 4 16 272 "751d51e303be1208a7a463bebb6d7ae04a92db5b5abe7d5b102980f20c9044b1"
    "0000006000000000\nfffffec000000000\n0000038000000000\nfffffdc000000000\n\
     0000004202244000\nffffffa8e5400000\n00000278c0000000\nfffffdc000000000\n\
     00000040e5d00000\n0000003bb4000000\n0000017f00000000\nfffffdc000000000\n\
     0000004ebf4e4000\n0000008421400000\n00000092c0000000\nfffffdc000000000\n"

/-- Part 1 of the coefficients: 4 cells. -/
def coef1 : ℕ → ℕ :=
  pinned_hex% 64 4 16 272 "ed25ed6b3faf3828c265690ed5dd83b2dd4a6f6f2329c76e0b269d824860c763"
    "00000060fc000000\n0000008d40000000\nffffffb400000000\nfffffdc000000000\n\
     0000006ff39e4000\n0000006181400000\nfffffee2c0000000\nfffffdc000000000\n\
     000000767fd00000\n0000000ab4000000\nfffffe1f00000000\nfffffdc000000000\n\
     000000719a144000\nffffff9205400000\nfffffd68c0000000\nfffffdc000000000\n"

/-- Part 0 of the bounds: 4 cells. -/
def bound0 : ℕ → ℕ :=
  pinned_hex% 64 4 4 68 "b56a09fc14e3603884e1586bf332a47daa64c2a511e446ed5f3788d84df253e0"
    "000000a794dbc004\n0000005d8dee0004\n00000051b0f7c004\n0000006373b48004\n"

/-- Part 1 of the bounds: 4 cells. -/
def bound1 : ℕ → ℕ :=
  pinned_hex% 64 4 4 68 "318e10c1da4320637faf77d7f86afa6f3ac0dff61f5184f42b51a63131216437"
    "0000007439e1c004\n0000007f7eb50004\n0000007da783c004\n0000008334288004\n"

/-- The blocks of the mesh: a part has one block. -/
def meshBlocks (b : ℕ) : ℕ := (nat_tree% [mesh0, mesh1, mesh2]) (Nat.div b 1) (Nat.mod b 1)

/-- The blocks of the coefficients: a part has four blocks. -/
def coefBlocks (b : ℕ) : ℕ := (nat_tree% [coef0, coef1]) (Nat.div b 4) (Nat.mod b 4)

/-- The blocks of the bounds: a part has one block. -/
def boundBlocks (b : ℕ) : ℕ := (nat_tree% [bound0, bound1]) (Nat.div b 1) (Nat.mod b 1)

/-- Entry `i` of table `t`: the mesh is table 0, the coefficients table 1, the bounds
table 2. -/
def look (t i : ℕ) : ℕ :=
  (nat_tree% [blockSlot 64 4 meshBlocks, blockSlot 64 4 coefBlocks, blockSlot 64 4 boundBlocks])
    t i

/-- The second mesh point is stored as `39 · 2 ^ 32`, with the bias `2 ^ 63` of a slot. -/
theorem look_mesh_one : look 0 1 = 2 ^ 63 + 39 * 2 ^ 32 := by decide +kernel

/-- The last coefficient, entry 31 of the table and entry 15 of its second part, is `-9 / 4`
at the scale `2 ^ -40`. -/
theorem look_coef_last : look 1 31 = 2 ^ 63 - 9 * 2 ^ 38 := by decide +kernel

/-! ### The tests, in two ranges -/

/-- The tests of the cells 0 to 3 pass. -/
cert_shard shard0 : (test (total look)) (below := 8) (start := 0) (count := 4) (batch := 2)
  (unfolding := [test, cellCond, stored, «local», coefAt, meshAt, boundAt, entryBall, gridBall])

/-- The tests of the cells 4 to 7 pass. -/
cert_shard shard1 : (test (total look)) (below := 8) (start := 4) (count := 4) (batch := 2)
  (unfolding := [test, cellCond, stored, «local», coefAt, meshAt, boundAt, entryBall, gridBall])

/-- The tests of all 8 cells pass. -/
cert_aggregate all : (test (total look)) (below := 8) (shards := shard, 2)

/-! ### The statement over the real numbers -/

/-- Mesh point `k` of the stored data, a real number. -/
noncomputable def x (k : ℕ) : ℝ := storedVal look (.mesh k)

/-- Coefficient `j` of cell `k` of the stored data. -/
noncomputable def c (k j : ℕ) : ℝ := storedVal look (.coef k j)

/-- The bound of cell `k` of the stored data. -/
noncomputable def b (k : ℕ) : ℝ := storedVal look (.bound k)

/-- **The table inequality on the stored mesh.** For each of the 8 cells `k` of the invented
data and every real `t` between the mesh points `x k` and `x (k + 1)`, the cubic of the cell is
at most the bound `b k`. The proof is the test of every cell, evaluated in two ranges. -/
theorem cubic_le_bound (k : ℕ) (hk : k < 8) (t : ℝ) (hlo : x k ≤ t) (hhi : t ≤ x (k + 1)) :
    c k 0 + (t - x k) * (c k 1 + (t - x k) * (c k 2 + (t - x k) * c k 3)) ≤ b k :=
  cell_bound (stored_encloses fun _ _ _ ↦ total_eq_some) (all ⟨k, hk⟩) t hlo hhi

/-- There is a certificate for 8 cells: the pattern of a final theorem that assumes
`Nonempty (CellCert n)`. The checker of `MeshSpec` accepts the stored tables. -/
theorem nonempty_cert : Nonempty (CellCert 8) :=
  Check.nonempty_of_run (storedChecker 8) ⟨look, storedChecker_run fun k hk ↦ all ⟨k, hk⟩⟩

/-! ### A run over byte strings -/

/-- The text of mesh point 0, in the format of a run: the line `0000000000000000`. -/
def runMesh0 : ByteArray :=
  ⟨#[48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 10]⟩

/-- The text of mesh point 1: the line `0000002700000000`. -/
def runMesh1 : ByteArray :=
  ⟨#[48, 48, 48, 48, 48, 48, 50, 55, 48, 48, 48, 48, 48, 48, 48, 48, 10]⟩

/-- The text of mesh point 2: the line `0000004c00000000`. -/
def runMesh2 : ByteArray :=
  ⟨#[48, 48, 48, 48, 48, 48, 52, 99, 48, 48, 48, 48, 48, 48, 48, 48, 10]⟩

/-- The text of the four coefficients of cell 0: the first four lines of `coef0`. -/
def runCoef0 : ByteArray :=
  ⟨#[48, 48, 48, 48, 48, 48, 54, 48, 48, 48, 48, 48, 48, 48, 48, 48, 10,
    102, 102, 102, 102, 102, 101, 99, 48, 48, 48, 48, 48, 48, 48, 48, 48, 10,
    48, 48, 48, 48, 48, 51, 56, 48, 48, 48, 48, 48, 48, 48, 48, 48, 10,
    102, 102, 102, 102, 102, 100, 99, 48, 48, 48, 48, 48, 48, 48, 48, 48, 10]⟩

/-- The text of the four coefficients of cell 1: the next four lines of `coef0`. -/
def runCoef1 : ByteArray :=
  ⟨#[48, 48, 48, 48, 48, 48, 52, 50, 48, 50, 50, 52, 52, 48, 48, 48, 10,
    102, 102, 102, 102, 102, 102, 97, 56, 101, 53, 52, 48, 48, 48, 48, 48, 10,
    48, 48, 48, 48, 48, 50, 55, 56, 99, 48, 48, 48, 48, 48, 48, 48, 10,
    102, 102, 102, 102, 102, 100, 99, 48, 48, 48, 48, 48, 48, 48, 48, 48, 10]⟩

/-- The text of the bound of cell 0: the line `000000a794dbc004`. -/
def runBound0 : ByteArray :=
  ⟨#[48, 48, 48, 48, 48, 48, 97, 55, 57, 52, 100, 98, 99, 48, 48, 52, 10]⟩

/-- The text of the bound of cell 1: the line `0000005d8dee0004`. -/
def runBound1 : ByteArray :=
  ⟨#[48, 48, 48, 48, 48, 48, 53, 100, 56, 100, 101, 101, 48, 48, 48, 52, 10]⟩

/-- A manifest of seven byte strings for the first two cells of the stored tables, one cell in
each shard: three mesh points in parts of one, the coefficients in two parts of four and two
bounds in parts of one, thirteen entries of 64 bits. -/
def runManifest : Run.Manifest where
  tables := [
    ⟨64, 1, [.of "mesh-0" runMesh0, .of "mesh-1" runMesh1, .of "mesh-2" runMesh2]⟩,
    ⟨64, 4, [.of "coef-0" runCoef0, .of "coef-1" runCoef1]⟩,
    ⟨64, 1, [.of "bound-0" runBound0, .of "bound-1" runBound1]⟩]
  count := 2
  shard := 1
  halo := 1

/-- The byte strings of the manifest: part `p` of table `t`, and the empty text for a part that
the manifest does not list. -/
def runTexts (t p : ℕ) : ByteArray :=
  Nat.rec
    (Nat.rec runMesh0 (fun p _ ↦ Nat.rec runMesh1
      (fun p _ ↦ Nat.rec runMesh2 (fun _ _ ↦ ByteArray.empty) p) p) p)
    (fun t _ ↦ Nat.rec
      (Nat.rec runCoef0 (fun p _ ↦ Nat.rec runCoef1 (fun _ _ ↦ ByteArray.empty) p) p)
      (fun t _ ↦ Nat.rec
        (Nat.rec runBound0 (fun p _ ↦ Nat.rec runBound1 (fun _ _ ↦ ByteArray.empty) p) p)
        (fun _ _ ↦ ByteArray.empty) t) t) t

/-- **The tables of the byte strings are the stored tables.** The thirteen entries that the run
reads from its texts are the entries of the first two cells of `look`: three mesh points, eight
coefficients and two bounds. The kernel reads both, the texts line by line with `hexEntry?` and
the stored tables from their literals. -/
theorem run_look : (∀ i, i < 3 → Run.look runManifest runTexts 0 i = look 0 i) ∧
    (∀ i, i < 8 → Run.look runManifest runTexts 1 i = look 1 i) ∧
    (∀ i, i < 2 → Run.look runManifest runTexts 2 i = look 2 i) := by
  decide +kernel

/-- The byte strings are those of the manifest: a listed part has the length and the digest of
its pin, and a part of a window that is not listed is empty. -/
theorem run_matches : Run.Matches runManifest runTexts := by
  intro t p hw
  -- A part in the window of one of the two shards is one of the parts 0, 1, 2.
  have hp : p < 3 := by
    obtain ⟨j, hj, -, hjp⟩ := hw
    simp only [runManifest] at hj hjp
    omega
  rcases t with _ | _ | _ | t <;> interval_cases p <;>
    first
    | exact Run.Pin.of_ok _ _
    | rfl

/-- The tests of both shards pass on the byte strings of `runManifest`, texts in the format of
a run with entries of 64 bits, each through the window of its shard; the kernel evaluates
them. -/
theorem run_shards (j : ℕ) (hj : j * runManifest.shard < runManifest.count) :
    Run.shardOk runManifest test runTexts j = true := by
  have hj : j < 2 := by simpa [runManifest] using hj
  interval_cases j <;> cert_eval [Run.shardOk]

/-- **The hypothesis of a run can be met.** `Run.Ok runManifest test` holds: the seven byte
strings match the manifest (`run_matches`) and the tests of both shards pass on them
(`run_shards`). -/
theorem run_ok : Run.Ok runManifest test :=
  Run.ok_of_windows (by decide) run_matches fun j hj ↦
    ⟨runTexts, fun _ _ _ _ ↦ rfl, run_shards j hj⟩

/-- **The run proves the inequality of its two cells.** For the cells `k = 0, 1` of the stored
tables and every real `t` between the mesh points `x k` and `x (k + 1)`, the cubic of the cell
is at most the bound `b k`. This is the statement of `cubic_le_bound` for these cells, proved
here by the other route: from the shard tests of the run over the byte strings
(`MeshSpec.cells_of_shardOk`) and the fact that the byte strings hold the stored entries
(`run_look`). So the build and the run give the same statement about the same numbers. -/
theorem run_cubic_le_bound (k : ℕ) (hk : k < 2) (t : ℝ) (hlo : x k ≤ t) (hhi : t ≤ x (k + 1)) :
    c k 0 + (t - x k) * (c k 1 + (t - x k) * (c k 2 + (t - x k) * c k 3)) ≤ b k := by
  obtain ⟨hm, hc, hb⟩ := run_look
  have h := holds_cellCond.mp
    (cells_of_shardOk (m := runManifest) (by decide) run_shards (k := k) hk fun _ ↦ 0) t
  -- The entries of cell `k` that the run read are the stored ones.
  simp only [storedVal, hm k (by omega), hm (k + 1) (by omega), hc (4 * k + 0) (by omega),
    hc (4 * k + 1) (by omega), hc (4 * k + 2) (by omega), hc (4 * k + 3) (by omega),
    hb k hk] at h
  exact h hlo hhi

/-- The certificate for two cells that `MeshSpec.nonempty_of_run` gives from the run. -/
theorem nonempty_of_tiny_run : Nonempty (CellCert 2) := nonempty_of_run run_ok

end CAS.Examples.Cert.Mesh

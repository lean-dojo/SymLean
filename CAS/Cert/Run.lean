/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Cert.Range
public import CAS.Cert.Table
public import CAS.Cert.HexText

/-!
# A run of a test over files, as a hypothesis

## Motivation

Some certificates are too large for any build: hundreds of gigabytes of tables, which no module
can embed. A program can still read the files part by part and test every index. What does such
a run establish, how is it stated in Lean without an axiom, and which statement about the real
numbers follows from it?

## The idea

A `Manifest` lists the files: for every table the width of an entry, the number of entries in a
part, and for every part its file name, length and SHA-256 digest. The indices of the family of
tests are cut into shards of `shard` indices; shard `j` reads parts `j, …, j + halo` of every
table and nothing else (`windowLook`), so the program holds a few parts at a time.

`Run.Ok m family` is a proposition: `0 < m.shard`, and there are byte strings with the lengths
and digests of the manifest (`Matches`) on which the test of every shard passes (`shardOk`). It
is existential on purpose. A run tests one family of byte strings, and two different byte
strings can share a digest, so a run does not establish a statement about all byte strings with
these digests.
Nothing in this library proves `Run.Ok` for a manifest of files. A theorem that uses a run
takes `Run.Ok m family` as a hypothesis, in its statement, where a reader sees it.

What follows from a run is proved here once. The lookup of a window returns `none` outside the
window, and a test turns `none` into an invalid ball ([Table](Table.lean)), so each passing
index was tested on entries of the whole table `look m texts` (`Ok.exists_texts`). No property
of the family is needed, in particular no proof about which entries it reads. The conclusion
keeps the byte strings and the fact that they have the lengths and digests of the manifest, so
a statement that follows from a run is about the tables of such byte strings and not about
tables that merely exist. Inside a window an entry is absent as well when its line is not in
the format of [HexText](HexText.lean): in a part that the manifest does not list, whose text is
empty by `Matches`, in a short text, at a byte that is not a digit. The ball of an absent entry
is invalid, so every comparison that passed was between balls of well-formed entries of listed
parts, and a comparison that reads a malformed or missing line fails, with or without the
comparison of digests. A condition can still pass without such an entry
([Table](Table.lean)).

`exec` is the program: for each shard it reads the files of the window, compares their lengths
and digests with the manifest, and evaluates `shardOk` on them. `main` is its command line. No
theorem is about `exec`: that its result is the conjunction of these comparisons and tests is
read from its code.

## Main results

* `look_of_windowLook` (all manifests): an entry that a window returns is the entry of the
  whole table.
* `shardOk_congr` (all manifests, all families): the test of shard `j` depends only on the
  parts `j, …, j + halo`. So the value that `exec` computes from the files it holds is the
  value of `shardOk` on all files.
* `ok_of_windows` (all manifests, all families): if every shard passes on byte strings that
  agree with the files on its window, then `Run.Ok`. This is the step from what the program
  evaluates to the proposition.
* `test_of_shardOk` (all manifests, all families, all byte strings): if the tests of all shards
  pass on given byte strings, every index below `count` passes its test on the window of its
  shard.
* `Ok.exists_texts` (all manifests, all families): from a run, byte strings with the lengths
  and digests of the manifest such that every index below `count` passed its test on a partial
  lookup that agrees with their tables.
* `Run.Ok`, `Run.Matches`, `Run.shardOk` (definitions); `Run.exec`, `Run.main` (the program).

## Relations

`ok_of_windows` is `shardOk_congr` at every shard. `test_of_shardOk` is `natAll_spec` for the
shard of the index, and `Ok.exists_texts` is `test_of_shardOk` with `look_of_windowLook` at the
byte strings of the run.
`MeshSpec.cells_of_run` ([MeshSpec](../Examples/Cert/MeshSpec.lean)) turns it, for every
manifest `m`, into the conditions of all cells on the tables of byte strings with the digests of
`m`, with `enclosesReal_entryBall?` ([Table](Table.lean)), and `MeshSpec.nonempty_of_run` into
`Nonempty (CellCert m.count)`: the form `∀ input, run input = success → Nonempty CertType`.
[Mesh](../Examples/Cert/Mesh.lean) proves `Run.Ok` in the kernel for a manifest of seven
short byte strings, so the hypothesis can be met. `cert_shard` ([Shard](Shard.lean)) is the
same family of tests on data that the build embeds, checked by the kernel.

## Scope

Whether a run happened is not a theorem. A run trusts what `TRUST.md` lists under "A run over
files": the program that evaluates the Lean functions (Lean's compiler and interpreter or a C
compiler, and the runtime), the reading of the files, and the script that starts the processes
and collects their results. The digests name the files of a run for a reader who repeats it.
They stay in the conclusion of `Ok.exists_texts` as `Matches`, and no proof draws anything from
them: that the byte strings of the conclusion are the files a reader holds would need the
collision resistance of SHA-256, which is not a theorem. The text format is fixed: one entry per
line, as `w / 4` hexadecimal digits and a line feed ([HexText](HexText.lean)). The width of a
table in the manifest is the width of its text; the family of tests fixes the bias and the scale
with which it reads the entries, and nothing ties the two. The kernel does not evaluate SHA-256
as it is written in [Sha256](Sha256.lean), so the small instance pins its byte strings by the
digest function itself.
-/

@[expose] public section

namespace CAS.Cert.Run

open CAS.Numerics

/-- One file of a run. -/
structure Pin where
  /-- The path of the file, relative to the directory of the data. -/
  file : String
  /-- The length of the file in bytes. -/
  bytes : ℕ
  /-- The SHA-256 digest of the file in lowercase hexadecimal, as `sha256sum` prints it. -/
  sha256 : String

namespace Pin

/-- The byte string has the length and the digest of the pin. -/
def ok (pin : Pin) (text : ByteArray) : Bool :=
  text.size == pin.bytes && Sha256.hex (Sha256.hash text) == pin.sha256

/-- The pin of a byte string: its length and its digest. -/
def of (file : String) (text : ByteArray) : Pin :=
  ⟨file, text.size, Sha256.hex (Sha256.hash text)⟩

/-- A byte string has its own pin. -/
theorem of_ok (file : String) (text : ByteArray) : (of file text).ok text = true := by
  simp [ok, of]

end Pin

/-- One table of a run, stored in parts. -/
structure Table where
  /-- The width of an entry in bits, a multiple of 4. -/
  width : ℕ
  /-- The number of entries in each part. -/
  perPart : ℕ
  /-- The files of the parts, part `0` first. -/
  parts : List Pin

/-- The files of a run and the cut of its indices into shards. -/
structure Manifest where
  /-- The tables. -/
  tables : List Table
  /-- The number of indices of the family of tests. -/
  count : ℕ
  /-- The number of indices in a shard. -/
  shard : ℕ
  /-- Shard `j` reads the parts `j, …, j + halo` of every table. -/
  halo : ℕ

/-- Table `t` of the manifest, and a table without parts past the end. -/
def Manifest.table (m : Manifest) (t : ℕ) : Table := m.tables.getD t ⟨0, 1, []⟩

/-- The byte strings `texts t p` are those of the manifest on every part `p` of every table `t`
that lies in the window of some shard: a part that the manifest lists has the length and the
digest of its pin, and a part that it does not list is the empty text, which has no entries.
These are the parts that a run over all shards reads, and `exec` holds the empty text for a part
that is not listed. A part outside every window is not constrained. -/
def Matches (m : Manifest) (texts : ℕ → ℕ → ByteArray) : Prop :=
  ∀ t p : ℕ, (∃ j, j * m.shard < m.count ∧ j ≤ p ∧ p ≤ j + m.halo) →
    match (m.table t).parts[p]? with
    | some pin => pin.ok (texts t p) = true
    | none => texts t p = ByteArray.empty

/-- Entry `i` of table `t`, read from the texts of all parts by `hexEntry?`
([HexText](HexText.lean)): `none` when its line is not in the format, as in a part whose text
is missing or short. -/
def look? (m : Manifest) (texts : ℕ → ℕ → ByteArray) (t i : ℕ) : Option ℕ :=
  hexEntry? (m.table t).width (texts t (i / (m.table t).perPart)) (i % (m.table t).perPart)

/-- The tables of the byte strings: entry `i` of table `t`, and `0`, the biased form of
`-2 ^ (w - 1)`, where the line of the entry is not in the format. A test does not read such an
entry as a number: it reads through `windowLook`, where the entry is absent. -/
def look (m : Manifest) (texts : ℕ → ℕ → ByteArray) (t i : ℕ) : ℕ := (look? m texts t i).getD 0

/-- Entry `i` of table `t` as shard `j` sees it: the entry, if it lies in one of the parts
`j, …, j + halo` and its line is in the format, and `none` otherwise. -/
def windowLook (m : Manifest) (texts : ℕ → ℕ → ByteArray) (j t i : ℕ) : Option ℕ :=
  if j ≤ i / (m.table t).perPart ∧ i / (m.table t).perPart ≤ j + m.halo then
    look? m texts t i
  else none

/-- An entry that the window of a shard returns is the entry of the whole table. -/
theorem look_of_windowLook {m : Manifest} {texts : ℕ → ℕ → ByteArray} {j t i v : ℕ}
    (h : windowLook m texts j t i = some v) : look m texts t i = v := by
  unfold windowLook at h
  split at h
  · rw [look, h, Option.getD_some]
  · exact absurd h (by simp)

/-- The window of shard `j` depends only on the parts `j, …, j + halo`. -/
theorem windowLook_congr {m : Manifest} {texts texts' : ℕ → ℕ → ByteArray} {j : ℕ}
    (h : ∀ t p, j ≤ p → p ≤ j + m.halo → texts t p = texts' t p) :
    windowLook m texts j = windowLook m texts' j := by
  funext t i
  unfold windowLook
  split
  · rename_i hw
    rw [look?, look?, h t _ hw.1 hw.2]
  · rfl

/-- The test of shard `j`: the family `family`, reading through the window of the shard, passes
at the indices `j * shard, …` of the shard that are below `count`. -/
def shardOk (m : Manifest) (family : (ℕ → ℕ → Option ℕ) → ℕ → Bool)
    (texts : ℕ → ℕ → ByteArray) (j : ℕ) : Bool :=
  natAll (min m.shard (m.count - j * m.shard)) fun k ↦
    family (windowLook m texts j) (j * m.shard + k)

/-- **A shard reads its window only.** If two families of byte strings agree on the parts
`j, …, j + halo`, the test of shard `j` has the same value on both. The program evaluates the
test on the parts it holds, and this is the value on all files. -/
theorem shardOk_congr {m : Manifest} {family : (ℕ → ℕ → Option ℕ) → ℕ → Bool}
    {texts texts' : ℕ → ℕ → ByteArray} {j : ℕ}
    (h : ∀ t p, j ≤ p → p ≤ j + m.halo → texts t p = texts' t p) :
    shardOk m family texts j = shardOk m family texts' j := by
  unfold shardOk
  rw [windowLook_congr h]

/-- **A run.** A shard has at least one index (`0 < m.shard`), and there are byte strings that
match the manifest `m` (`Matches`: for the parts in the window of some shard, the lengths and
digests of the listed parts, and no text for a part that is not listed) on which the test of
every shard passes, for the family `family`. This is what a run of `exec` over all shards
reports; it is used as a hypothesis and proved nowhere for files. -/
def Ok (m : Manifest) (family : (ℕ → ℕ → Option ℕ) → ℕ → Bool) : Prop :=
  0 < m.shard ∧ ∃ texts : ℕ → ℕ → ByteArray, Matches m texts ∧
    ∀ j, j * m.shard < m.count → shardOk m family texts j = true

/-- **What the program establishes.** Let `0 < m.shard` and let `texts` be byte strings that
match the manifest (`Matches`). If for every shard `j` the test of the shard passes on some byte
strings that agree with `texts` on the parts `j, …, j + halo`, as the parts that `exec` holds
do, then `Run.Ok m family`. -/
theorem ok_of_windows {m : Manifest} {family : (ℕ → ℕ → Option ℕ) → ℕ → Bool} (hs : 0 < m.shard)
    {texts : ℕ → ℕ → ByteArray} (hm : Matches m texts)
    (h : ∀ j, j * m.shard < m.count → ∃ held : ℕ → ℕ → ByteArray,
      (∀ t p, j ≤ p → p ≤ j + m.halo → held t p = texts t p) ∧
        shardOk m family held j = true) :
    Ok m family :=
  ⟨hs, texts, hm, fun j hj ↦
    let ⟨_, hagree, hrun⟩ := h j hj
    (shardOk_congr hagree).symm.trans hrun⟩

/-- **Every index is tested through the window of its shard.** If `0 < m.shard` and the tests
of all shards pass on the byte strings `texts`, then every index `k < m.count` passes its test
`family` on the window of shard `k / m.shard`, a partial lookup whose entries are entries of
the tables `look m texts` (`look_of_windowLook`). This is the statement of the shard tests for
given byte strings; the index `k` is index `k % m.shard` of shard `k / m.shard`. -/
theorem test_of_shardOk {m : Manifest} {family : (ℕ → ℕ → Option ℕ) → ℕ → Bool}
    {texts : ℕ → ℕ → ByteArray} (hs : 0 < m.shard)
    (hall : ∀ j, j * m.shard < m.count → shardOk m family texts j = true) {k : ℕ}
    (hk : k < m.count) : family (windowLook m texts (k / m.shard)) k = true := by
  have hdiv := Nat.div_add_mod' k m.shard
  have hj : k / m.shard * m.shard < m.count := by omega
  have := natAll_spec (hall _ hj) (j := k % m.shard)
    (lt_min (Nat.mod_lt _ hs) (by omega))
  rwa [hdiv] at this

/-- **What a run proves.** From `Run.Ok m family` there are byte strings `texts` that match the
manifest (`Matches m texts`: the lengths and digests of its listed parts in the windows of the
shards) such that every index
`k < m.count` passed the test `family look? k` on a partial lookup `look?` whose entries are
entries of the tables `look m texts` of these byte strings. A soundness theorem for the family
on partial lookups then gives the statement about the tables of byte strings with the digests
of the manifest, as `MeshSpec.cells_of_run` does.

The byte strings are those of the run, and the partial lookup of `k` is the window of its
shard (`test_of_shardOk`). -/
theorem Ok.exists_texts {m : Manifest} {family : (ℕ → ℕ → Option ℕ) → ℕ → Bool}
    (h : Ok m family) :
    ∃ texts : ℕ → ℕ → ByteArray, Matches m texts ∧ ∀ k, k < m.count →
      ∃ look? : ℕ → ℕ → Option ℕ,
        (∀ t i v, look? t i = some v → look m texts t i = v) ∧ family look? k = true := by
  obtain ⟨hs, texts, hm, hall⟩ := h
  exact ⟨texts, hm, fun k hk ↦
    ⟨windowLook m texts (k / m.shard), fun t i v ↦ look_of_windowLook,
      test_of_shardOk hs hall hk⟩⟩

/-! ### The program -/

/-- Runs the shards `lo, …, hi - 1`: for each shard, reads from the directory `dir` the files
of its window that are not held from the shard before, compares their lengths with the manifest,
and their digests too when `digest` is set, and evaluates `shardOk` on the parts it holds.
Returns `true` if every comparison and every test passed, and `false` when `m.shard = 0`, where
a shard has no index. An empty range `hi ≤ lo` has nothing to compare or test and returns
`true`; `main` refuses it. A part of the window that the manifest does not list is the empty
text, which has no entries. It holds at most `halo + 2` parts of every table at a time. -/
def exec (m : Manifest) (family : (ℕ → ℕ → Option ℕ) → ℕ → Bool) (dir : System.FilePath)
    (lo hi : ℕ) (digest : Bool) : IO Bool := do
  if m.shard == 0 then return false
  let mut pass := true
  -- `window[t][q]` is part `at + q` of table `t`.
  let mut window : Array (Array ByteArray) := #[]
  let mut «at» := 0
  for j in [lo:hi] do
    let mut next : Array (Array ByteArray) := #[]
    for t in [0:m.tables.length] do
      let mut row : Array ByteArray := #[]
      for q in [0:m.halo + 1] do
        let held := if j == «at» + 1 then (window[t]?).bind (·[q + 1]?) else none
        match held, (m.table t).parts[j + q]? with
        | some text, _ => row := row.push text
        | none, none => row := row.push ByteArray.empty
        | none, some pin =>
          let text ← IO.FS.readBinFile (dir / pin.file)
          unless (if digest then pin.ok text else text.size == pin.bytes) do
            IO.eprintln s!"{pin.file}: not the file of the manifest"
            pass := false
          row := row.push text
      next := next.push row
    window := next
    «at» := j
    let parts := window
    let texts : ℕ → ℕ → ByteArray := fun t p ↦
      ((parts[t]?.getD #[])[p - j]?).getD ByteArray.empty
    unless shardOk m family texts j do
      IO.eprintln s!"shard {j}: the test fails"
      pass := false
  return pass

/-- The command line of a run: `DIR [LO HI] [--no-digest]`. Runs the shards `LO, …, HI - 1`
(all shards by default) on the files under `DIR` and returns `0` if all of them pass. It
returns `1` for a range that is empty or ends after the last shard, so that a result `0` always
stands for at least one tested shard. With `--no-digest` only the lengths of the files are
compared; their digests must then be compared by another program. -/
def main (m : Manifest) (family : (ℕ → ℕ → Option ℕ) → ℕ → Bool) (args : List String) :
    IO UInt32 := do
  let digest := !args.contains "--no-digest"
  let shards := (m.count + m.shard - 1) / m.shard
  let usage := s!"usage: DIR [LO HI] [--no-digest], with 0 ≤ LO < HI ≤ {shards}"
  let parsed : Option (String × ℕ × ℕ) :=
    match args.filter (· != "--no-digest") with
    | [dir] => some (dir, 0, shards)
    | [dir, lo, hi] => lo.toNat?.bind fun lo ↦ hi.toNat?.map fun hi ↦ (dir, lo, hi)
    | _ => none
  let some (dir, lo, hi) := parsed
    | IO.eprintln usage; return 1
  if m.shard == 0 || hi ≤ lo || shards < hi then
    IO.eprintln usage
    return 1
  let pass ← exec m family dir lo hi digest
  IO.println s!"shards {lo} to {hi} of {shards}: {if pass then "pass" else "FAIL"}\
    {if digest then "" else " (digests not compared)"}"
  return if pass then 0 else 1

end CAS.Cert.Run

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
import Lean.Data.Json

/-!
# The modules of a certificate in shards, written from a manifest

`lake env lean --run scripts/CertStubs.lean MANIFEST.json [ROOT] [--run]` writes, under the
directory `dir` of the manifest (relative to `ROOT`, by default the current directory), the
modules of a certificate whose family of tests has too many indices for one module.

Without `--run`, for a build (the kernel, or compiled code under `cega.nativeCertificates`):

* `Part<j>.lean`: part `j` of every table, read from a data file whose length and SHA-256 digest
  are written in the module and stored as literals of `block` entries (`pinned_hex%`);
* `Tables.lean`: the parts of every table joined, and `look t i`, entry `i` of table `t`;
* `Shard<j>.lean`: the range of indices of shard `j`, by `cert_shard`;
* `All.lean`: the statement for all indices, by `cert_aggregate`.

A manifest without tables is a certificate whose data are recomputed: only the shards and
`All.lean` are written, and the family is a constant of type `ℕ → Bool`.

With `--run`, for a run over files that no module embeds:

* `Manifest.lean`: the manifest as a term `manifest : CAS.Cert.Run.Manifest`, which a theorem
  with the hypothesis `CAS.Cert.Run.Ok manifest family` names;
* `RunMain.lean`: the program `CAS.Cert.Run.main manifest family`, to be run by
  `lake env lean --run`.

The manifest is a JSON object with the fields `prefix` (the module prefix), `dir`, `spec` (the
module that defines the family of tests), `family` (a constant of type
`(ℕ → ℕ → Option ℕ) → ℕ → Bool`: the tables as a lookup function that may hold only some
entries, then the index), `count` (the number of indices), `shard` (indices per shard module),
`batch` (indices per kernel declaration), `unfolding` (definitions that `cert_eval` unfolds),
`halo` (optional, for a run: how many parts after its own a shard reads, by default one),
`block` (optional, for a build: the number of entries in one literal, by default 4096, which
must divide `perPart`) and `tables`: for each table its `name`, `width` in bits, `perPart`
entries per part, and `parts` with `file`, `bytes`, `sha256` and `entries` for each part. In a
run, a shard is the indices of one part of the first table.

The script only writes text. Nothing it writes is trusted: every module is checked by Lean when
it is built, and the program of a run evaluates the functions of `CAS.Cert.Run`.
-/

open Lean

/-- One part of a table in the manifest. -/
structure Part where
  file : String
  bytes : Nat
  sha256 : String
  entries : Nat
  deriving FromJson, Inhabited

/-- One table of the manifest. -/
structure Table where
  name : String
  width : Nat
  perPart : Nat
  parts : Array Part
  deriving FromJson, Inhabited

/-- The manifest. -/
structure Manifest where
  «prefix» : String
  dir : String
  spec : String
  family : String
  count : Nat
  shard : Nat
  batch : Nat
  unfolding : Array String
  halo : Option Nat
  block : Option Nat
  tables : Array Table
  deriving FromJson

/-- The number of entries in one literal of a build. -/
def Manifest.blockSize (m : Manifest) : Nat := m.block.getD 4096

/-- The header of a written module. -/
def header (imports : Array String) (title body : String) : String :=
  let lines := imports.foldl (init := "") fun acc m ↦
    acc ++ s!"public import {m}\npublic meta import {m}\n"
  "/-\nCopyright (c) 2026 SymLean Team. All rights reserved.\n\
   Released under Apache 2.0 license as described in the file LICENSE.\n\
   Authors: SymLean Team\n-/\n\nmodule\n\n" ++ lines ++
  s!"\n/-!\n# {title}\n\n{body}\n\nWritten by `scripts/CertStubs.lean` from the manifest of the \
     certificate; do not edit.\n-/\n\n@[expose] public section\n\n"

/-- A list of terms as `a, b, c`, broken into lines of at most 96 characters. -/
def wrapList (items : Array String) (indent : String) : String := Id.run do
  let mut out := ""
  let mut line := indent
  for i in [0:items.size] do
    let item := items[i]! ++ (if i + 1 < items.size then "," else "")
    if line.length + item.length + 1 > 96 && line.length > indent.length then
      out := out ++ line.trimAsciiEnd.toString ++ "\n"
      line := indent
    line := line ++ item ++ " "
  return out ++ line.trimAsciiEnd.toString

/-- The module of part `j`. -/
def partModule (m : Manifest) (j : Nat) : String := Id.run do
  let mut text := header #["CAS.Cert.Shard"] s!"Part {j} of the tables of `{m.prefix}`"
    s!"Each definition is the function from a block index to a literal of {m.blockSize} \
       entries, read from a\ndata file whose length and SHA-256 digest are written here; the \
       build fails if the file differs.\nThe literals establish nothing about their entries."
  text := text ++ s!"namespace {m.prefix}.Part{j}\n\n"
  for t in m.tables do
    if h : j < t.parts.size then
      let p := t.parts[j]
      text := text ++ s!"/-- Part {j} of the table `{t.name}`: {p.entries} entries of {t.width} \
        bits. -/\ndef {t.name} : ℕ → ℕ :=\n  pinned_hex% {t.width} {m.blockSize} {p.entries} \
        {p.bytes}\n    \"{p.sha256}\"\n    (include_str \"{p.file}\")\n\n"
  return text ++ s!"end {m.prefix}.Part{j}\n"

/-- The number of part modules: the largest number of parts of a table. -/
def partCount (m : Manifest) : Nat := m.tables.foldl (fun n t ↦ max n t.parts.size) 0

/-- The module of the tables. -/
def tablesModule (m : Manifest) : String := Id.run do
  let imports := (Array.range (partCount m)).map fun j ↦ s!"{m.prefix}.Part{j}"
  let mut text := header (#["CAS.Cert.Shard"] ++ imports) s!"The tables of `{m.prefix}`"
    "The parts of each table are joined by a selection tree, and `look t i` is entry `i` of \
     table `t`."
  text := text ++ s!"namespace {m.prefix}\n\nopen CAS.Cert CAS.Numerics\n\n"
  for t in m.tables do
    let parts := (Array.range t.parts.size).map fun j ↦ s!"Part{j}.{t.name}"
    let perPart := t.perPart / m.blockSize
    text := text ++ s!"/-- The blocks of the table `{t.name}`: {perPart} in each part. -/\n\
      def {t.name}Blocks (b : ℕ) : ℕ :=\n  (nat_tree% [\n{wrapList parts "    "}])\n    \
      (Nat.div b {perPart}) (Nat.mod b {perPart})\n\n"
  let tables := m.tables.map fun t ↦ s!"blockSlot {t.width} {m.blockSize} {t.name}Blocks"
  text := text ++ s!"/-- Entry `i` of table `t`: " ++
    ", ".intercalate (m.tables.mapIdx fun i t ↦ s!"`{t.name}` is table {i}").toList ++
    s!". -/\ndef look (t i : ℕ) : ℕ :=\n  (nat_tree% [\n{wrapList tables "    "}]) t i\n\n"
  return text ++ s!"end {m.prefix}\n"

/-- The number of shard modules. -/
def shardCount (m : Manifest) : Nat := (m.count + m.shard - 1) / m.shard

/-- The family of the statement: the family of the manifest on the tables, or the family itself
when the certificate has no tables. -/
def statedFamily (m : Manifest) : String :=
  if m.tables.isEmpty then m.family else s!"({m.family} (total look))"

/-- The module of shard `j`. -/
def shardModule (m : Manifest) (j : Nat) : String := Id.run do
  let start := j * m.shard
  let count := min m.shard (m.count - start)
  let range := s!"(below := {m.count}) (start := {start}) (count := {count}) \
    (batch := {m.batch})"
  let title := s!"Shard {j} of `{m.prefix}`: the indices {start} to {start + count - 1}"
  if m.tables.isEmpty then
    -- Recomputed data: the family is evaluated as it is.
    return header #["CAS.Cert.Shard", m.spec] title "The tests of these indices pass." ++
      s!"namespace {m.prefix}\n\nopen CAS.Cert\n\n\
         /-- The tests of the indices {start} to {start + count - 1} pass. -/\n\
         cert_shard shard{j} : {m.family}\n  {range}\n  \
         (unfolding := [\n{wrapList m.unfolding "    "}])\n\nend {m.prefix}\n"
  let unfolding := m.unfolding ++ #["CAS.Cert.entryBall", "CAS.Cert.gridBall"]
  return header #[s!"{m.prefix}.Tables", m.spec] title "The tests of these indices pass." ++
    s!"namespace {m.prefix}\n\nopen CAS.Cert\n\n\
       /-- The tests of the indices {start} to {start + count - 1} pass. -/\n\
       cert_shard shard{j} : {statedFamily m}\n  {range}\n  \
       (unfolding := [\n{wrapList unfolding "    "}])\n\nend {m.prefix}\n"

/-- The module of the aggregate. -/
def allModule (m : Manifest) : String :=
  let imports := (Array.range (shardCount m)).map fun j ↦ s!"{m.prefix}.Shard{j}"
  header imports s!"All {m.count} indices of `{m.prefix}`"
    s!"The {shardCount m} shards are joined into one statement for all indices, in a balanced \
       tree\n(`cert_aggregate`)." ++
  s!"namespace {m.prefix}\n\nopen CAS.Cert\n\n\
     /-- The tests of all {m.count} indices pass. -/\n\
     cert_aggregate all : {statedFamily m}\n  (below := {m.count}) (shards := shard, \
     {shardCount m})\n\nend {m.prefix}\n"

/-- The module of the manifest of a run. -/
def manifestModule (m : Manifest) : String := Id.run do
  let mut text := header #["CAS.Cert.Run"] s!"The files of the run of `{m.prefix}`"
    "The manifest of a run over files: for every part of every table the name, the length and \
     the\nSHA-256 digest of its file. A theorem that uses the run takes \
     `CAS.Cert.Run.Ok manifest family` as a\nhypothesis; this module proves nothing about the \
     files."
  text := text ++ s!"namespace {m.prefix}\n\n/-- The files of the run: " ++
    ", ".intercalate (m.tables.mapIdx fun i t ↦ s!"`{t.name}` is table {i}").toList ++
    s!";\n{m.count} indices in shards of {m.shard}. -/\n\
       def manifest : CAS.Cert.Run.Manifest where\n  tables := [\n"
  for i in [0:m.tables.size] do
    let t := m.tables[i]!
    let pins := t.parts.map fun p ↦ s!"      ⟨\"{p.file}\", {p.bytes},\n        \"{p.sha256}\"⟩"
    text := text ++ s!"    ⟨{t.width}, {t.perPart}, [\n" ++ ",\n".intercalate pins.toList ++
      "]⟩" ++ (if i + 1 < m.tables.size then ",\n" else "]\n")
  text := text ++ s!"  count := {m.count}\n  shard := {m.shard}\n  halo := {m.halo.getD 1}\n\n"
  return text ++ s!"end {m.prefix}\n"

/-- The program of a run. -/
def runMain (m : Manifest) : String :=
  s!"import {m.prefix}.Manifest\nimport {m.spec}\n\n\
     /-- The run of `{m.family}` over the files of `{m.prefix}.manifest`:\n\
     `DIR [LO HI] [--no-digest]`. Written by `scripts/CertStubs.lean`; do not edit. -/\n\
     def main (args : List String) : IO UInt32 :=\n  \
     CAS.Cert.Run.main {m.prefix}.manifest {m.family} args\n"

/-- Reads the manifest and writes the modules. -/
def main (args : List String) : IO UInt32 := do
  let run := args.contains "--run"
  let (path, root) ← match args.filter (· != "--run") with
    | [path] => pure (path, ".")
    | [path, root] => pure (path, root)
    | _ => IO.eprintln "usage: CertStubs.lean MANIFEST.json [ROOT] [--run]"; return 1
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let m : Manifest ← IO.ofExcept (fromJson? json)
  if m.shard == 0 || m.batch == 0 || m.blockSize == 0 then
    IO.eprintln "the manifest needs positive shard, batch and block sizes"; return 1
  let dir : System.FilePath := System.FilePath.mk root / m.dir
  IO.FS.createDirAll dir
  if run then
    if m.tables.isEmpty || m.shard != m.tables[0]!.perPart then
      IO.eprintln "in a run, a shard is the indices of one part of the first table"; return 1
    IO.FS.writeFile (dir / "Manifest.lean") (manifestModule m)
    IO.FS.writeFile (dir / "RunMain.lean") (runMain m)
    IO.println s!"{m.prefix}: Manifest and RunMain written to {dir}"
    return 0
  if m.tables.any (·.perPart % m.blockSize != 0) then
    IO.eprintln "the number of entries of a part is not a multiple of the block length"
    return 1
  for j in [0:partCount m] do
    IO.FS.writeFile (dir / s!"Part{j}.lean") (partModule m j)
  unless m.tables.isEmpty do
    IO.FS.writeFile (dir / "Tables.lean") (tablesModule m)
  for j in [0:shardCount m] do
    IO.FS.writeFile (dir / s!"Shard{j}.lean") (shardModule m j)
  IO.FS.writeFile (dir / "All.lean") (allModule m)
  IO.println s!"{m.prefix}: {partCount m} part modules, {shardCount m} shard modules\
    {if m.tables.isEmpty then "" else ", Tables"} and All written to {dir}"
  return 0

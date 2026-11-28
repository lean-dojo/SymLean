#!/bin/bash
# Copyright (c) 2026 SymLean Team. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Tests of the certificate framework (`CAS/Cert`) that cannot be part of `lake build`: compiled
# test vectors, the messages of refused statements, the native profile, and a certificate whose
# modules are written from a manifest and whose data are files, which the library does not embed.
#
# 1. Each `tests/cert/*.lean` is elaborated against the built library; `#guard` and `#guard_msgs`
#    turn every mismatch into an error.
# 2. Invented tables for 64 cells are written by `scripts/cert_synthetic.py`, the modules of their
#    certificate by `scripts/CertStubs.lean`, and `lean` compiles them outside Lake: the parts,
#    the tables, two shards and the aggregate, in the kernel and once more with compiled code.
#    The condition of every cell is stated over the real numbers and its axioms are compared.
#    Then the same for 256 cells in blocks of 8,192 bits, which are compact literals.
# 3. The same for tables with one spoiled bound: the shard of that cell must fail.
# 4. A certificate without tables, whose data are recomputed (`CAS.Examples.Cert.Seed`).
# 5. The run over files (`CAS.Cert.Run`): the program passes on the invented tables, on each
#    half of the shards, refuses an empty range and a range past the end, fails on the spoiled
#    tables, on a file whose digest differs, on a line that is not in the format and on a
#    missing file, and the statement with the run as a hypothesis has the standard axioms.
# A check that must fail also compares the message, so that it fails for the reason it names.
#
# Run from the repository root after `lake build`; it needs python3 and no network. About 50
# runs of `lean`, 3 to 10 s each, up to three at a time. The exit status is the result.
set -u
cd "$(dirname "$0")/../.."
status=0
work="$(mktemp -d "${TMPDIR:-/tmp}/symlean-cert.XXXXXX")"
trap 'rm -rf "$work"' EXIT
# expect NAME 0|1 COMMAND...: the command must succeed (0) or fail (1).
expect() {
  local name=$1 want=$2 got
  shift 2
  if "$@" > "$work/log" 2>&1; then got=0; else got=1; fi
  if [[ $got == "$want" ]]; then
    echo "ok   $name"
  else
    echo "FAIL $name"
    tail -n 12 "$work/log" | cut -c1-300 | sed 's/^/     /'
    status=1
  fi
}
# refuse NAME TEXT COMMAND...: the command must fail, and its output must contain TEXT, so
# that it fails for the reason that the check names.
refuse() {
  local name=$1 text=$2
  shift 2
  if "$@" > "$work/log" 2>&1; then
    echo "FAIL $name: the command passed"
    status=1
  elif grep -qF -- "$text" "$work/log"; then
    echo "ok   $name"
  else
    echo "FAIL $name: it failed without the message '$text'"
    tail -n 12 "$work/log" | cut -c1-300 | sed 's/^/     /'
    status=1
  fi
}
build() { lake env bash tests/cert/build.sh "$work/src" "$@"; }
stubs() { lake env lean --run scripts/CertStubs.lean "$@"; }
# check OUT FILE: elaborates FILE against the library and the modules of OUT.
check() { lake env bash -c 'LEAN_PATH="$1:$LEAN_PATH" lean -DwarningAsError=true "$2"' _ "$1" "$2"; }
# kernel_axioms OUT FILE NAME: Lean elaborates FILE, reports the axioms of NAME, and none of
# them comes from a native evaluation or a hole.
kernel_axioms() {
  local text
  text="$(check "$1" "$2")" || return 1
  grep -qF "'$3' depends on axioms" <<<"$text" || return 1
  ! grep -q '_native\|sorryAx' <<<"$text"
}
# native_axioms OUT FILE PATTERN: Lean elaborates FILE and its report, on one line, matches
# PATTERN.
native_axioms() {
  local text
  text="$(check "$1" "$2")" || return 1
  tr -d '\n' <<<"$text" | grep -q "$3"
}
# run OUT MAIN ARGS...: the program MAIN of a run, on the modules of OUT.
run() { lake env bash -c 'LEAN_PATH="$1:$LEAN_PATH" lean --run "${@:2}"' _ "$@"; }

for file in tests/cert/*.lean; do
  expect "$file" 0 lake env lean -DwarningAsError=true "$file"
done

# 2. A stored mesh in two shards, in the kernel.
mesh="$work/src/Stored/Mesh"
python3 scripts/cert_synthetic.py "$mesh" --cells 64 --per-part 32 --prefix Stored.Mesh \
  --dir Stored/Mesh > /dev/null
expect "modules of a stored certificate written" 0 stubs "$mesh/manifest.json" "$work/src"
expect "parts: seven files pinned by length and SHA-256" 0 \
  build "$work/out" 3 Stored.Mesh.Part0 Stored.Mesh.Part1 Stored.Mesh.Part2
expect "tables" 0 build "$work/out" 1 Stored.Mesh.Tables
expect "two shards, in the kernel" 0 build "$work/out" 2 Stored.Mesh.Shard0 Stored.Mesh.Shard1
expect "aggregate" 0 build "$work/out" 1 Stored.Mesh.All
cat > "$work/Kernel.lean" <<'LEAN'
import Stored.Mesh.All
open CAS.Cert CAS.Examples.Cert.MeshSpec
-- The statement about the stored numbers: the condition of every cell, over the real numbers.
theorem cells (k : ℕ) (hk : k < 64) (σ : ℕ → ℝ) :
    (cellCond k).holds (storedVal Stored.Mesh.look) σ :=
  Cond.holds_of_run (stored_encloses fun _ _ _ ↦ total_eq_some) (cellCond k) σ
    (Stored.Mesh.all ⟨k, hk⟩)
/-- info: 'cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cells
-- The pattern of a final theorem: a certificate from the checker and the passing tests.
theorem cert : Nonempty (CellCert 64) :=
  Check.nonempty_of_run (storedChecker 64)
    ⟨Stored.Mesh.look, storedChecker_run fun k hk ↦ Stored.Mesh.all ⟨k, hk⟩⟩
/-- info: 'cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cert
LEAN
expect "statements from the kernel build: standard axioms" 0 check "$work/out" "$work/Kernel.lean"

# The same shards with compiled code: the axioms of native evaluation appear.
cp -R "$work/out" "$work/native"
LEAN_OPTS=-Dweak.cega.nativeCertificates=true expect "two shards, compiled code" 0 \
  build "$work/native" 2 Stored.Mesh.Shard0 Stored.Mesh.Shard1
expect "aggregate of the native shards" 0 build "$work/native" 1 Stored.Mesh.All
printf 'import Stored.Mesh.All\n#print axioms Stored.Mesh.all\n' > "$work/Native.lean"
expect "native build: the axioms name the native evaluation" 0 native_axioms "$work/native" \
  "$work/Native.lean" \
  'Stored.Mesh.shard0.batch0._native.cegaFast.*Stored.Mesh.shard1.batch0._native.cegaFast'

# 2b. Blocks of 8,192 bits, which `pinned_hex%` stores as compact literals: the kernel reads
#     their definitions, and compiled code reads them through `natCompactImpl`.
compact="$work/src/Compact/Mesh"
python3 scripts/cert_synthetic.py "$compact" --cells 256 --per-part 128 --block 128 \
  --prefix Compact.Mesh --dir Compact/Mesh > /dev/null
expect "modules of a certificate with compact literals written" 0 \
  stubs "$compact/manifest.json" "$work/src"
expect "parts in blocks of 8,192 bits" 0 \
  build "$work/out" 3 Compact.Mesh.Part0 Compact.Mesh.Part1 Compact.Mesh.Part2
expect "tables of compact literals" 0 build "$work/out" 1 Compact.Mesh.Tables
expect "two shards on compact literals, in the kernel" 0 \
  build "$work/out" 2 Compact.Mesh.Shard0 Compact.Mesh.Shard1
expect "aggregate on compact literals" 0 build "$work/out" 1 Compact.Mesh.All
printf 'import Compact.Mesh.All\n#print axioms Compact.Mesh.all\n' > "$work/Compact.lean"
expect "kernel build on compact literals: no native axiom" 0 \
  kernel_axioms "$work/out" "$work/Compact.lean" Compact.Mesh.all
cp -R "$work/out" "$work/native2"
LEAN_OPTS=-Dweak.cega.nativeCertificates=true \
  expect "two shards on compact literals, compiled code" 0 \
  build "$work/native2" 2 Compact.Mesh.Shard0 Compact.Mesh.Shard1
expect "aggregate of the native shards on compact literals" 0 \
  build "$work/native2" 1 Compact.Mesh.All
expect "native build on compact literals: the axioms name the native evaluation" 0 \
  native_axioms "$work/native2" "$work/Compact.lean" \
  'Compact.Mesh.shard0.batch0._native.cegaFast.*Compact.Mesh.shard1.batch0._native.cegaFast'

# 3. One spoiled bound: the shard of cell 5 fails, the other one passes.
broken="$work/src/Broken/Mesh"
python3 scripts/cert_synthetic.py "$broken" --cells 64 --per-part 32 --prefix Broken.Mesh \
  --dir Broken/Mesh --break 5 > /dev/null
expect "modules of the spoiled certificate written" 0 stubs "$broken/manifest.json" "$work/src"
expect "spoiled parts" 0 build "$work/out" 3 Broken.Mesh.Part0 Broken.Mesh.Part1 Broken.Mesh.Part2
expect "spoiled tables" 0 build "$work/out" 1 Broken.Mesh.Tables
refuse "the shard of the spoiled cell is refused by the kernel" \
  "the kernel did not reduce the decision procedure" build "$work/out" 1 Broken.Mesh.Shard0
expect "the other shard passes" 0 build "$work/out" 1 Broken.Mesh.Shard1

# 4. Recomputed data: a manifest without tables.
mkdir -p "$work/src/Recomputed"
cat > "$work/src/Recomputed/manifest.json" <<'JSON'
{"prefix": "Recomputed", "dir": "Recomputed", "spec": "CAS.Examples.Cert.Seed",
 "family": "(CAS.Examples.Cert.Seed.test 8)", "count": 256, "shard": 128, "batch": 64,
 "unfolding": ["CAS.Examples.Cert.Seed.test", "CAS.Examples.Cert.MeshSpec.cellCond",
  "CAS.Examples.Cert.MeshSpec.meshAt", "CAS.Examples.Cert.MeshSpec.coefAt",
  "CAS.Examples.Cert.MeshSpec.boundAt", "CAS.Examples.Cert.MeshSpec.local",
  "CAS.Examples.Cert.Seed.benv", "CAS.Examples.Cert.Seed.genBenv",
  "CAS.Examples.Cert.Seed.taylor", "CAS.Examples.Cert.Seed.seedBall",
  "CAS.Examples.Cert.Seed.center", "CAS.Examples.Cert.Seed.meshBall", "CAS.Cert.gridBall"],
 "tables": []}
JSON
expect "modules of a recomputed certificate written" 0 \
  stubs "$work/src/Recomputed/manifest.json" "$work/src"
expect "two shards on recomputed tables" 0 build "$work/out" 2 Recomputed.Shard0 Recomputed.Shard1
expect "aggregate of the recomputed shards" 0 build "$work/out" 1 Recomputed.All

# 5. The run over files.
expect "modules of the run written" 0 stubs "$mesh/manifest.json" "$work/src" --run
expect "manifest of the run" 0 build "$work/out" 1 Stored.Mesh.Manifest
expect "run over all shards, digests by Lean's SHA-256" 0 \
  run "$work/out" "$mesh/RunMain.lean" "$mesh"
expect "run over the first shard" 0 run "$work/out" "$mesh/RunMain.lean" "$mesh" 0 1
expect "run over the second shard, lengths only" 0 \
  run "$work/out" "$mesh/RunMain.lean" "$mesh" 1 2 --no-digest
refuse "a run over no shard is refused" "usage: DIR" \
  run "$work/out" "$mesh/RunMain.lean" "$mesh" 1 1
refuse "a run past the last shard is refused" "usage: DIR" \
  run "$work/out" "$mesh/RunMain.lean" "$mesh" 0 3
expect "modules of the spoiled run written" 0 stubs "$broken/manifest.json" "$work/src" --run
expect "manifest of the spoiled run" 0 build "$work/out" 1 Broken.Mesh.Manifest
refuse "run over the spoiled tables fails at the shard of the spoiled cell" \
  "shard 0: the test fails" run "$work/out" "$broken/RunMain.lean" "$broken"
# One bound raised by one unit: the test still passes, the digest does not.
cp -R "$mesh" "$work/changed"
python3 - "$work/changed/data/bound-0.hex" <<'PY'
import sys
lines = open(sys.argv[1]).read().split('\n')
lines[0] = format(int(lines[0], 16) + 1, '016x')
open(sys.argv[1], 'w').write('\n'.join(lines))
PY
refuse "run on a changed file fails by its digest" "data/bound-0.hex: not the file of the manifest" \
  run "$work/out" "$mesh/RunMain.lean" "$work/changed"
expect "the same run without digests passes: lengths do not pin a file" 0 \
  run "$work/out" "$mesh/RunMain.lean" "$work/changed" --no-digest
# One digit replaced by a letter that is no digit: the entry is absent, so the test of the
# shard that reads it fails, also when no digest is compared.
cp -R "$mesh" "$work/malformed"
python3 - "$work/malformed/data/bound-0.hex" <<'PY'
import sys
lines = open(sys.argv[1]).read().split('\n')
lines[0] = lines[0][:-1] + 'g'
open(sys.argv[1], 'w').write('\n'.join(lines))
PY
refuse "run on a line that is not hexadecimal fails at the shard that reads it" \
  "shard 0: the test fails" run "$work/out" "$mesh/RunMain.lean" "$work/malformed" --no-digest
# A file that is missing: the program stops with the error of the read.
cp -R "$mesh" "$work/missing"
rm "$work/missing/data/bound-0.hex"
refuse "run with a missing file fails" "no such file or directory" \
  run "$work/out" "$mesh/RunMain.lean" "$work/missing"
cat > "$work/Run.lean" <<'LEAN'
import Stored.Mesh.Manifest
import CAS.Examples.Cert.MeshSpec
open CAS.Cert CAS.Examples.Cert.MeshSpec
-- The statement of the run: the condition of every cell for the tables of byte strings with
-- the lengths and digests of the manifest.
theorem cells (h : Run.Ok Stored.Mesh.manifest test) :
    ∃ texts, Run.Matches Stored.Mesh.manifest texts ∧ ∀ k, k < 64 → ∀ σ,
      (cellCond k).holds (storedVal (Run.look Stored.Mesh.manifest texts)) σ :=
  cells_of_run h
/-- info: 'cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cells
-- The pattern of a final theorem.
theorem cert (h : Run.Ok Stored.Mesh.manifest test) : Nonempty (CellCert 64) := nonempty_of_run h
/-- info: 'cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cert
LEAN
expect "statements from the run as a hypothesis: standard axioms" 0 \
  check "$work/out" "$work/Run.lean"
exit $status

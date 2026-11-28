/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
import CAS.Examples.Cert.Seed

/-!
# A range in the kernel, a range in compiled code, and the reuse of kernel theorems

`cert_shard` proves a range by `cert_eval`, which evaluates in the kernel unless
`cega.nativeCertificates` is set. With the option, compiled code evaluates the loops, and the
theorem depends on an axiom of native evaluation for each loop, which `#print axioms` shows;
the test below looks for the axiom of the first loop. The option would put such axioms into the
library, so this file is elaborated by `tests/cert/run.sh` against the built library instead of
being part of `lake build`.

A loop whose statement the kernel has already proved in the same file is not evaluated again:
with the option set, `cert_eval` finds the kernel theorem and uses it, and no axiom of native
evaluation appears. The batches of `cert_shard` are elaborated one after the other, so the
theorems of an earlier shard are found. The three shards are therefore: the first 64 cells in
the kernel, the next 64 cells in compiled code, and the first 64 cells again with the option,
which reuses the kernel theorems. No range is evaluated by both routes.
-/

open CAS.Cert CAS.Examples.Cert

set_option linter.hashCommand false

/-- The tests of 64 cells of the recomputed tables, in the kernel. -/
cert_shard byKernel : (Seed.test 8) (below := 256) (start := 0) (count := 64) (batch := 32)
  (unfolding := [Seed.test, MeshSpec.cellCond, MeshSpec.meshAt, MeshSpec.coefAt,
    MeshSpec.boundAt, MeshSpec.local, Seed.benv, Seed.genBenv, Seed.taylor, Seed.seedBall,
    Seed.center, Seed.meshBall, gridBall])

/-- info: 'byKernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms byKernel

set_option cega.nativeCertificates true in
/-- The tests of the next 64 cells, evaluated by compiled code. -/
cert_shard byCompiledCode : (Seed.test 8) (below := 256) (start := 64) (count := 64) (batch := 32)
  (unfolding := [Seed.test, MeshSpec.cellCond, MeshSpec.meshAt, MeshSpec.coefAt,
    MeshSpec.boundAt, MeshSpec.local, Seed.benv, Seed.genBenv, Seed.taylor, Seed.seedBall,
    Seed.center, Seed.meshBall, gridBall])

-- The names of the axioms end in a counter of auxiliary declarations, which is not pinned.
/--
info: 'byCompiledCode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 byCompiledCode.batch0._native.cegaFast.ax_
-/
#guard_msgs (info, substring := true) in
#print axioms byCompiledCode

set_option cega.nativeCertificates true in
/-- The first 64 cells again, with the option: the loops are those of `byKernel`, whose kernel
theorems are used. -/
cert_shard byKernelAgain : (Seed.test 8) (below := 256) (start := 0) (count := 64) (batch := 32)
  (unfolding := [Seed.test, MeshSpec.cellCond, MeshSpec.meshAt, MeshSpec.coefAt,
    MeshSpec.boundAt, MeshSpec.local, Seed.benv, Seed.genBenv, Seed.taylor, Seed.seedBall,
    Seed.center, Seed.meshBall, gridBall])

/-- info: 'byKernelAgain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms byKernelAgain

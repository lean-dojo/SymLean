/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
import CAS
import FloatLib.Floats.Formats.BinaryInterchange.Configured.KernelPath

/-!
# The order and the failure reports of native `cega [fast]`

With `cega.nativeCertificates`, `cega [fast]` first decides a closed statement about floats with
`float_decide`, in the kernel, and then makes its native attempts. A failing `cega [fast]`
restores the state after its native attempts and runs the kernel routes. When those fail too,
the report keeps the failure of the native attempts after the kernel's.
-/

/--
The native attempt of `cega [fast]`, before this kernel fallback, failed with:
  Finite native attempt: CEGA finite certificate evaluates to false
-/
#guard_msgs (substring := true, whitespace := lax) in
set_option cega.nativeCertificates true in
example : ∀ i : Fin 2, i.val = 0 := by
  cega [fast]

-- A statement about floats is decided by `float_decide` before any native attempt, so its proof
-- has no native axiom.
set_option cega.nativeCertificates true in
/-- The binary64 sum `1.5 + 2.25 = 3.75`, proved by native `cega [fast]` through `float_decide`. -/
theorem fast_float : (1.5 : FloatLib.Floats.Binary64) + 2.25 = 3.75 := by
  cega [fast]

/-- info: 'fast_float' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fast_float

-- A false statement about floats: the report of the native attempts starts with the refusal of
-- `float_decide`, and then the native certificate refutes the statement.
/--
The native attempt of `cega [fast]`, before this kernel fallback, failed with:
  float_decide: cega float_decide route: the kernel did not evaluate
    1.5 + 2.25 = 3.5
  to `true` after FloatLib's kernel rules rewrote its float operations. The statement may be
  false; `float_decide` on its own says whether it is.
  Finite native attempt: CEGA finite certificate evaluates to false
-/
#guard_msgs (substring := true, whitespace := lax) in
set_option cega.nativeCertificates true in
example : (1.5 : FloatLib.Floats.Binary64) + 2.25 = 3.5 := by
  cega [fast]

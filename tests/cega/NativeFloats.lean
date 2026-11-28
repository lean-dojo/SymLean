/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
import CAS

/-!
# `cega [fast]` in a float arithmetic, with native checking on

With `cega.nativeCertificates`, `cega [fast]` evaluates the enclosure of a polynomial box query
with compiled code, FloatLib's `Backend.rational` through its `@[csimp]` rules, and the theorem
shows the native certificate among its axioms. A float enclosure, FloatLib's evaluation with the
ends of a binary format, is evaluated in the kernel only, also on a subdivided box. So the same
goal proved by `cega [fast, use_floats]`, or by `cega [fast]` where the option `cega.arithmetic`
is a float format, has the three standard axioms and no native one.
-/

set_option cega.nativeCertificates true

/-- The exact enclosure of a polynomial, evaluated by compiled code. -/
theorem fastExact (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * x + x ≤ 2 := by
  cega [fast]

/-- The binary64 enclosure of the same polynomial, evaluated by the kernel. -/
theorem fastFloats (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * x + x ≤ 2 := by
  cega [fast, use_floats]

set_option cega.arithmetic "binary64" in
/-- The same, with the format from the option. -/
theorem fastOption (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * x + x ≤ 2 := by
  cega [fast]

/-- A binary64 enclosure after six bisections of the box, evaluated by the kernel. -/
theorem fastFloatsDeep (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 0.26 := by
  cega [fast, use_floats] (depth := 6)

/-- info: 'fastExact' depends on axioms: [propext, Classical.choice, Quot.sound, fastExact._native.cegaFast.ax_1 -/
#guard_msgs (substring := true) in
#print axioms fastExact

/-- info: 'fastFloats' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fastFloats

/-- info: 'fastOption' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fastOption

/-- info: 'fastFloatsDeep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fastFloatsDeep

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
import CAS.Numerics.NatLiteral
import CAS.Numerics.ComputedLiteral

/-!
# Compiled code reads a large literal from its decimal fields

`nat_literal%` and `computed_nat%` store a value of at least `2 ^ 4096` with a second definition
that compiled code runs in its place and that reads the value from a string of decimal fields
(`CAS/Numerics/CompactLiteral.lean`). No proof reads that string, so only compiled code can show
that it holds the same number as the literal: `#eval` below compares each literal, read by
compiled code outside the evaluation of the importers, with the power it was computed from. The
library has no such literal, since `scripts/audit.sh` lists every compiled implementation, so
the test is here.

The last test reads the definitions that store the two literals: their bodies are raw literals,
not numerals. With numerals as bodies the kernel is slow on a declaration that unfolds many such
definitions whose numbers agree in their low 64 bits. A literal below `2 ^ 4096`
keeps its numeral, which the third entry shows. The test sees the form of the body, not the
time.
-/

/-- A literal of 5072 bits, with no zero field among its 85 fields of 60 bits. -/
def literalPower : Nat := nat_literal% (3 ^ 3200)

example : literalPower = 3 ^ 3200 := by decide +kernel

/-- info: (true, 5072) -/
#guard_msgs in
#eval (decide (literalPower = 3 ^ 3200), literalPower.log2 + 1)

/-- A value of 4212 bits, which `computed_nat%` stores as a named definition as well. -/
def computedPower : Nat := computed_nat% (7 ^ 1500)

example : computedPower = 7 ^ 1500 := by decide +kernel

/-- info: (true, 4212) -/
#guard_msgs in
#eval (decide (computedPower = 7 ^ 1500), computedPower.log2 + 1)

/-- A literal of 159 bits, below the size from which a literal is stored in the compact form. -/
def smallPower : Nat := nat_literal% (3 ^ 100)

open Lean in
/-- info: [true, true, false] -/
#guard_msgs in
run_meta do
  let env ← getEnv
  -- Whether the value of `c` names a definition whose body is a raw literal.
  let raw (c : Name) : Bool := (env.find? c).any fun info ↦ info.value?.any fun v ↦
    v.getUsedConstants.any fun a ↦ (env.find? a).any fun i ↦ i.value?.any (·.isRawNatLit)
  logInfo m!"{[raw ``literalPower, raw ``computedPower, raw ``smallPower]}"

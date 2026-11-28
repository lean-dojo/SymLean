/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Cert.Shard
public meta import CAS.Cert.Shard
public import CAS.Numerics.CompactRows
public meta import CAS.Numerics.CompactRows

/-!
# Tables computed during elaboration

## Motivation

`pinned_hex%` ([Shard](Shard.lean)) stores a table that an outside program wrote to a text.
Reading the text is the expensive part of a certificate with large witnesses: every digit and
the digest go through interpreted code. A witness that a short program can compute from much
smaller data need not be stored at all.

## The idea

`computed_tables% e` evaluates the closed term `e : Array (Array ℕ)` once, with compiled code,
while the declaration is elaborated, and stands for the function `ℕ → ℕ → ℕ` that sends `j` and
`i` to the literal of `e[j][i]`. The literals are named auxiliary definitions, as those of
`pinned_hex%`, and the two selections are the trees of `nat_tree%`. So a module can compute its
witness tables from a seed and keep them in its object file, where the kernel and later modules
read them. Several tables come from one evaluation, since a witness computation usually yields
several (a factor, its weights, a matrix that it passes on).

## Main definitions

* `computed_tables% e`: the term elaborator.
* `flattenTables`: the tables as one array, the value that the elaborator evaluates.

## Relations

`computed_nat%` ([ComputedLiteral](../Numerics/ComputedLiteral.lean)) is the same for one
number, and `computed_rows%` ([CompactRows](../Numerics/CompactRows.lean)) evaluates a row
function at every index and packs all rows into one literal, in the row trees of the importers.
`computed_tables%` gives the block functions that the tables of a certificate use
([Table](Table.lean)): each entry is a literal of its own, read without splitting a larger one.

## Implementation notes

The elaborator evaluates `fun _ ↦ flattenTables e` with `evalRowFun`
([CompactRows](../Numerics/CompactRows.lean)) and calls it once, so `e` is computed once and no
evaluator of its own is needed. The evaluation runs inside `withLiteralEnv`
([CompactLiteral](../Numerics/CompactLiteral.lean)),
so the compact literals that `e` reads, for instance the tables of imported modules, come from
their definitions. A module that evaluates a term using definitions of an imported module
imports it with `meta import` as well. Neither `e` nor the compiled code that evaluates it is
trusted: the kernel sees only the literals, which establish nothing about their entries. A
certificate checks them.

A table of long rows is read fast by the kernel because `mkCompactNatLiteral` stores raw
literals: with numerals as bodies, a kernel declaration that reads many rows that agree in their
lowest slot is slow ([CompactLiteral](../Numerics/CompactLiteral.lean), implementation notes).
-/

public meta section

namespace CAS.Cert

open Lean Elab Term Meta CAS.Numerics

/-- The number of tables of `t`, their lengths and then their entries, as one array: the form
in which `computed_tables%` reads the value of its term through `evalRowFun`. -/
def flattenTables (t : Array (Array Nat)) : Array Nat :=
  t.foldl (· ++ ·) (#[t.size] ++ t.map (·.size))

/--
`computed_tables% e`

is the function `ℕ → ℕ → ℕ` that sends `j` and `i` to the literal of the entry `e[j][i]` of the
closed term `e : Array (Array ℕ)`, which compiled code evaluates once while the declaration is
elaborated. An index past the end reads one of the entries. The elaborator fails if `e` has no
table or an empty table. The literals establish nothing about their entries.
-/
syntax (name := computedTables) "computed_tables% " term:max : term

elab_rules : term | `(computed_tables% $e) => do
  -- One call of one compiled function yields every table.
  let flat ← withLiteralEnv do
    let fn ← evalRowFun (← `(fun _ : Nat ↦ CAS.Cert.flattenTables $e))
    pure (fn 0)
  let count := flat.getD 0 0
  if count == 0 then throwErrorAt e "computed_tables% needs at least one table"
  let mut start := count + 1
  let mut parts := #[]
  for j in [0:count] do
    let size := flat.getD (j + 1) 0
    if size == 0 then throwErrorAt e "computed_tables% needs at least one entry in every table"
    let mut leaves := #[]
    for i in [0:size] do
      let name ← mkAuxDeclName `_computedTable
      let literal ← mkCompactNatLiteral name (flat.getD (start + i) 0)
      -- The literal stays data during elaboration; kernel and compiled checks read its body.
      setReducibilityStatus name .irreducible
      leaves := leaves.push literal
    start := start + size
    parts := parts.push (← chunkedTree (mkConst ``Nat) leaves)
  chunkedTree (← mkArrow (mkConst ``Nat) (mkConst ``Nat)) parts

end CAS.Cert

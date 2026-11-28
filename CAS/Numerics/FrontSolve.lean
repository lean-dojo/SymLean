/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.FrontTree

/-!
# The witnesses of a tree of fronts, computed during elaboration

## Motivation

The check of a tree of fronts ([FrontTree](FrontTree.lean)) reads, for every node, a factor
with its weights and the matrix that the node passes to its parent. They are witnesses: the
theorems hold for any tables that pass the row tests. Stored as texts they are several hundred
megabytes for a few thousand unknowns, and embedding them costs more than checking them. They
follow from the leaf matrices by exact integer arithmetic, so a build can compute them.

## The idea

`FrontTree.solveNode` computes the tables of one node from the rows of its leaf matrix, its
columns and the rows that its children pass up. It forms the assembled rows of the node with a
zero passed matrix and eliminates the pivots in order, with the row combinations of the check
itself (`ldltResidualRow`): the residual row of pivot `k` against the columns before it is row
`k` of the Schur complement of `a (front - β)`; its diagonal entry divided by `4 ^ sbits` and
rounded is the weight `d k`, and the row divided by `2 ^ sbits * d k` and rounded is column `k`
of the factor, with `2 ^ sbits` on the diagonal. For a row after the pivots the residual row
against all columns, divided by `a` and rounded, is the row of the passed matrix. A row after
the pivots in which no column has an entry is marked in the idle mask of the node, for
`fastRowCheck`. `FrontTree.solveTree` runs the nodes in order and hands each node the rows of
its children.

The functions are meant for `computed_tables%` ([Computed](../Cert/Computed.lean)), which
evaluates them with compiled code and turns their arrays into tables of literals. They prove
nothing and nothing is proved about them: the row tests of the tree, evaluated by the kernel on
the literals, decide whether the tables are good, and they fail if the matrix is not above its
lift or if an entry leaves its bounds.

## Main definitions

* `FrontTree.sparseRows`: the packed rows of a symmetric matrix from the triples (row, column,
  value) of its entries on and above the diagonal, the form in which a module stores a leaf
  matrix for `solveNode`.
* `FrontTree.solveNode`: the tables of one node: its leaf rows, the rows that it passes up, its
  factor columns, its packed weights and its idle mask.
* `FrontTree.solveTree`: the tables of all nodes, those of node `ξ` at the indices `5 ξ` to
  `5 ξ + 4`.

## Relations

The rows are packed with `biasedPack` and read with `signedSlot`
([PackedSlots](PackedSlots.lean)), slot by slot, and combined with `ldltResidualRow`
([PackedLDL](PackedLDL.lean)) on the assembled rows `asmRow` of [FrontTree](FrontTree.lean), so
the solver computes the numbers that the check then tests, with the same functions.

## Scope

The elimination has no pivoting and no test of its own: a failure shows only in the row tests.
The work is that of the check, one row combination per row, plus one slot at a time for the
rounding; it is not shared with the check, which the kernel then repeats on the literals.
-/

@[expose] public section

namespace CAS.Numerics.FrontTree

/-- The integer nearest to `x / m` for `m > 0`, halves upwards. -/
def roundDiv (x : ℤ) (m : ℕ) : ℤ := Int.ediv (x + Int.ofNat (m / 2)) (Int.ofNat m)

/-- The packed rows, of `n` biased slots of width `w`, of the symmetric matrix of size `n` whose
entries on and above the diagonal are the `count` triples (row, column, value) in the biased
slots of 64 bits of `entries`. Triples with the same position add up. These are the rows of that
matrix when every index lies in `0 … n - 1` and every entry of the sum fits a slot of width `w`.
Neither is tested here: an index outside that range, or an entry that does not fit, gives other
rows, and the theorems of the tree are about the rows that come out. -/
def sparseRows (w n entries count : ℕ) : Array ℕ := Id.run do
  let mut rows : Array ℤ := Array.replicate n 0
  for t in [0:count] do
    let i := (signedSlot 64 (3 * t) entries).toNat
    let j := (signedSlot 64 (3 * t + 1) entries).toNat
    let v := signedSlot 64 (3 * t + 2) entries
    rows := rows.modify i (· + v * Int.ofNat (1 <<< (w * j)))
    if i ≠ j then
      rows := rows.modify j (· + v * Int.ofNat (1 <<< (w * i)))
  return rows.map fun row ↦ (row + Int.ofNat (biasRow w n)).toNat

/-- The tables of node `ξ` of a tree with the shape and the sizes of `T` and the columns `C`,
computed from the rows `leaf` of its leaf matrix (without the columns) and from the rows
`kidRows p i` that its `p`-th child passes up (row `i` after the pivots of the child, in the
layout of the child). The tables are: the leaf rows; the rows after the pivots of the matrix
that `ξ` passes up; the factor columns, with `2 ^ sbits` on the diagonal; the weights, packed in
slots of 64 bits; the idle mask. The tables of `T` itself are not read. -/
def solveNode (T : FrontTree) (C : Cols) (sbits ξ : ℕ) (leaf : Array ℕ)
    (kidRows : ℕ → ℕ → ℕ) : Array (Array ℕ) := Id.run do
  let w := T.width
  let c := T.size ξ
  let r := T.rank ξ
  let bias := biasRow w c
  -- The tree that the solver reads: its leaf rows, the rows of its children, nothing passed up.
  let A : FrontTree := FrontTree.withCols
    { T with
      leaf := fun _ i ↦ leaf.getD i 0
      schur := fun η i ↦
        if η = ξ then bias else kidRows ((T.kids ξ).idxOf η) (i - T.rank η) } C
  let p := A.params ξ
  let asm := Array.ofFn (n := c) fun i ↦ A.asmRow ξ i.val
  let one := 1 <<< sbits
  let mut cols : Array ℕ := Array.mkEmpty r
  let mut d : Array ℕ := Array.mkEmpty r
  let mut touched := 0
  for k in [0:r] do
    let row := ldltResidualRow { p with rank := k } (fun i ↦ asm.getD i 0)
      (fun j ↦ cols.getD j 0) (fun j ↦ d.getD j 0) k
    let dk := (roundDiv (signedSlot w k row) (one * one)).toNat
    let col := biasedPack w c fun m ↦
      if m < k then 0 else if m = k then Int.ofNat one
      else roundDiv (signedSlot w m row) (dk * one)
    cols := cols.push col
    d := d.push dk
    touched := touched ||| (col ^^^ bias)
  let mut passed : Array ℕ := Array.mkEmpty (c - r)
  let mut idle := 0
  for n in [r:c] do
    let active := slot w n touched != 0
    let row := ldltResidualRow (if active then p else { p with rank := 0 }) (fun i ↦ asm.getD i 0)
      (fun j ↦ cols.getD j 0) (fun j ↦ d.getD j 0) n
    passed := passed.push <| biasedPack w c fun m ↦
      if m < r then 0 else roundDiv (signedSlot w m row) T.scale
    if !active then
      idle := idle ||| (slotMask w <<< (w * n))
  -- A table of `computed_tables%` has at least one entry.
  return #[leaf, if passed.isEmpty then #[0] else passed, if cols.isEmpty then #[0] else cols,
    #[packSlots 64 r fun k ↦ d.getD k 0], #[idle]]

/-- The tables of all nodes of a tree with the shape and the sizes of `T` and the columns `C`,
from the rows `leaf ξ` of the leaf matrices: the five tables of node `ξ` (`solveNode`) are at
the indices `5 ξ` to `5 ξ + 4`. The nodes are solved in order, every node after its children. -/
def solveTree (T : FrontTree) (C : Cols) (sbits : ℕ) (leaf : ℕ → Array ℕ) :
    Array (Array ℕ) := Id.run do
  let mut out : Array (Array ℕ) := Array.mkEmpty (5 * T.nodes)
  for ξ in [0:T.nodes] do
    let done := out
    out := out ++ solveNode T C sbits ξ (leaf ξ) fun p i ↦
      (done.getD (5 * (T.kids ξ).getD p 0 + 1) #[]).getD i 0
  return out

end CAS.Numerics.FrontTree

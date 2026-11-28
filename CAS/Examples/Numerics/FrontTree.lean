/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Cert.Computed
public meta import CAS.Cert.Computed
public import CAS.Numerics.FrontSolve
public meta import CAS.Numerics.FrontSolve

/-!
# A small tree of fronts

## Motivation

Does the test of [FrontTree](../../Numerics/FrontTree.lean) accept a factor that a program
computed in floating point, for a matrix that is not positive definite, and what does its
theorem then state?

## The idea

The matrix is invented: 14 unknowns on a lattice of points, every cell adding a matrix on
its corners, with entries scaled by `2 ^ 10`. In floating point it has one negative eigenvalue,
about `-27` in these units. The unknowns are eliminated along a tree of
7 nodes. For each node a program outside this repository (float64 on a GPU) computed columns
for the low eigenvalues of the pivot block of the front (one column in all),
the factor of the pivot block with the outer products of the columns added, and the matrix
passed to the parent, and rounded them to integers. The kernel evaluates the test of every
row of every node, and `FrontTree.uniform_le_global_cols` gives the bound. Nothing of the
factor or of the columns is trusted.

Of the rows, 4 are after the pivots of their node and have no factor entry: the
front of the node does not touch them. They are marked in a mask and pass the cheap
test `FrontTree.fastRowCheck`, which gives the full test by
`FrontTree.rowCheck_of_fast`.

The stored tables are witnesses, several times larger than the matrix. The last section
computes them instead. `FrontTree.solveTree` ([FrontSolve](../../Numerics/FrontSolve.lean))
eliminates the pivots of every node in exact integer arithmetic, from the entries of the
leaf matrices and the columns, while this module is compiled, and `computed_tables%`
([Computed](../../Cert/Computed.lean)) keeps the result as literals. The kernel evaluates
the same tests on them. That computation is not trusted either.

## Main results

* `assembled_ge` (one example): for every real vector `x`, `23` times the sum of the squares
  of the pivots of all nodes, which are all 14 unknowns, is at most the sum of the leaf
  forms plus the squares of the columns applied to `x`.
* `rows_fail` (one example): the same rows and factor do not pass the tests of the tree
  without the columns.
* `solved_ok` (one example): the factor, the weights, the passed rows and the idle mask that
  `FrontTree.solveTree` computes pass the node tests and the row tests in place of the
  stored ones.
* `solved_leaf` (one example): the leaf rows that it expands from the triples of the
  entries are the stored leaf rows.

## Relations

An instance of `FrontTree.uniform_le_global_cols`, and through it of
`FrontTree.uniform_le_global` at the tree `tree.withCols cols`. The tests are
`FrontTree.nodeCheck` and `FrontTree.rowCheck` of that tree, `FrontTree.colsCheck` and
`FrontTree.colsRowCheck`, with `FrontTree.idleCheck` and
`FrontTree.fastRowCheck` for the idle rows.
Larger trees store their rows in files and test them in shards
([Shard](../../Cert/Shard.lean)).

## Scope

One invented matrix. That the matrix itself has a negative direction is a computation in
floating point, not a theorem here. The numerals of the rows are written in the module,
which a larger tree cannot do; a larger tree stores the entries and the columns and
computes the tables of each node in a module of its own (`FrontTree.solveNode`). The
columns are data in both versions: nothing here finds them. The bound is stated for the
stored tables; for the computed ones the tests are proved, which are its hypotheses on
the factor.
-/

@[expose] public section

namespace CAS.Examples.Numerics.FrontTree

open CAS.Cert CAS.Numerics

/-- Row `i` of the leaf matrix of node `ξ`, as a packed row of biased slots. -/
def leafRows (ξ i : ℕ) : ℕ :=
  (([[0x8000000000000008000000000000007fffffffffffd6f7fffffffffffeb87fffffffffffeb8800000000000525,
      0x8000000000000008000000000000007fffffffffffeb87fffffffffffd6f8000000000005257fffffffffffeb8,
      0x8000000000000008000000000000007fffffffffffeb88000000000005257fffffffffffd6f7fffffffffffeb8,
      0x8000000000000008000000000000008000000000005257fffffffffffeb87fffffffffffeb87fffffffffffd6f,
      0x800000000000000800000000000000800000000000000800000000000000800000000000000800000000000000,
      0x800000000000000800000000000000800000000000000800000000000000800000000000000800000000000000],
    [0x7fffffffffffe847ffffffffffff437fffffffffffeb67ffffffffffff5c7fffffffffffe9f800000000000592,
      0x7ffffffffffff437fffffffffffe847ffffffffffff5c7fffffffffffeb68000000000005927fffffffffffe9f,
      0x8000000000000008000000000000007ffffffffffff5c8000000000002977fffffffffffeb67ffffffffffff5c,
      0x8000000000000008000000000000008000000000002977ffffffffffff5c7ffffffffffff5c7fffffffffffeb6,
      0x7ffffffffffff438000000000002fb8000000000000008000000000000007fffffffffffe847ffffffffffff43,
      0x8000000000002fb7ffffffffffff438000000000000008000000000000007ffffffffffff437fffffffffffe84],
    [0x800000000000000800000000000000800000000000000800000000000000,
      0x800000000000000800000000000000800000000000000800000000000000,
      0x800000000000000800000000000000800000000000000800000000000000,
      0x800000000000000800000000000000800000000000000800000000000000],
    [0x7fffffffffffdd47fffffffffffeeb7fffffffffffdbd7fffffffffffed77fffffffffffdc28000000000008c3,
      0x7fffffffffffeeb7fffffffffffdd47fffffffffffed77fffffffffffdbd8000000000008c37fffffffffffdc2,
      0x8000000000000008000000000000007fffffffffffed78000000000004687fffffffffffdbd7fffffffffffed7,
      0x8000000000000008000000000000008000000000004687fffffffffffed77fffffffffffed77fffffffffffdbd,
      0x7fffffffffffeeb80000000000045b8000000000000008000000000000007fffffffffffdd47fffffffffffeeb,
      0x80000000000045b7fffffffffffeeb8000000000000008000000000000007fffffffffffeeb7fffffffffffdd4],
    [0x8000000000000008000000000000007ffffffffffff0c7ffffffffffff7e7ffffffffffff7e8000000000001ca,
      0x8000000000000008000000000000007ffffffffffff7e7ffffffffffff0c8000000000001ca7ffffffffffff7e,
      0x8000000000000008000000000000007ffffffffffff7e8000000000001ca7ffffffffffff0c7ffffffffffff7e,
      0x8000000000000008000000000000008000000000001ca7ffffffffffff7e7ffffffffffff7e7ffffffffffff0c,
      0x800000000000000800000000000000800000000000000800000000000000800000000000000800000000000000,
      0x800000000000000800000000000000800000000000000800000000000000800000000000000800000000000000],
    [0x800000000000000800000000000000800000000000000800000000000000,
      0x800000000000000800000000000000800000000000000800000000000000,
      0x800000000000000800000000000000800000000000000800000000000000,
      0x800000000000000800000000000000800000000000000800000000000000],
    [0x800000000000000800000000000000,
      0x800000000000000800000000000000]] : List (List ℕ)).getD ξ []).getD i 0

/-- Row `i` of the matrix that node `ξ` passes up, in the layout of `ξ`. -/
def schurRows (ξ i : ℕ) : ℕ :=
  (([[0x800000000000000800000000000000800000000000000800000000000000800000000000000800000000000000,
      0x800000000000000800000000000000800000000000000800000000000000800000000000000800000000000000,
      0x8000000000000008000000000000007fffffffffffce080000000000030a800000000000000800000000000000,
      0x80000000000000080000000000000080000000000030a7fffffffffffce0800000000000000800000000000000,
      0x800000000000000800000000000000800000000000000800000000000000800000000000000800000000000000,
      0x800000000000000800000000000000800000000000000800000000000000800000000000000800000000000000],
    [0x800000000000000800000000000000800000000000000800000000000000800000000000000800000000000000,
      0x800000000000000800000000000000800000000000000800000000000000800000000000000800000000000000,
      0x7ffffffffffff827ffffffffffff707fffffffffffeef80000000000021a800000000000000800000000000000,
      0x7ffffffffffff707ffffffffffff8280000000000021a7fffffffffffeef800000000000000800000000000000,
      0x7fffffffffffeb28000000000002567ffffffffffff827ffffffffffff70800000000000000800000000000000,
      0x8000000000002567fffffffffffeb27ffffffffffff707ffffffffffff82800000000000000800000000000000],
    [0x800000000000000800000000000000800000000000000800000000000000,
      0x800000000000000800000000000000800000000000000800000000000000,
      0x7fffffffffffdfe800000000000195800000000000000800000000000000,
      0x8000000000001957fffffffffffdfe800000000000000800000000000000],
    [0x800000000000000800000000000000800000000000000800000000000000800000000000000800000000000000,
      0x800000000000000800000000000000800000000000000800000000000000800000000000000800000000000000,
      0x7ffffffffffff307ffffffffffff137fffffffffffdfb800000000000370800000000000000800000000000000,
      0x7ffffffffffff137ffffffffffff308000000000003707fffffffffffdfb800000000000000800000000000000,
      0x7fffffffffffe258000000000003797ffffffffffff307ffffffffffff13800000000000000800000000000000,
      0x8000000000003797fffffffffffe257ffffffffffff137ffffffffffff30800000000000000800000000000000],
    [0x800000000000000800000000000000800000000000000800000000000000800000000000000800000000000000,
      0x800000000000000800000000000000800000000000000800000000000000800000000000000800000000000000,
      0x8000000000000008000000000000007fffffffffffea08000000000000d4800000000000000800000000000000,
      0x8000000000000008000000000000008000000000000d47fffffffffffea0800000000000000800000000000000,
      0x800000000000000800000000000000800000000000000800000000000000800000000000000800000000000000,
      0x800000000000000800000000000000800000000000000800000000000000800000000000000800000000000000],
    [0x800000000000000800000000000000800000000000000800000000000000,
      0x800000000000000800000000000000800000000000000800000000000000,
      0x7fffffffffffc0580000000000014d800000000000000800000000000000,
      0x80000000000014d7fffffffffffc05800000000000000800000000000000],
    [0x800000000000000800000000000000,
      0x800000000000000800000000000000]] : List (List ℕ)).getD ξ []).getD i 0

/-- Column `i` of the factor of node `ξ`. -/
def factorCols (ξ i : ℕ) : ℕ :=
  (([[0x8000000000000008000000000000007ffffffffffdf5b7ffffffffffefb47ffffffffffefb4800000000004000,
      0x8000000000000008000000000000007ffffffffffe5ae7ffffffffffd8a7800000000004000800000000000000],
    [0x7ffffffffffee977fffffffffff7577fffffffffff0e27fffffffffff87d7ffffffffffefd4800000000004000,
      0x7fffffffffff20d7ffffffffffeb117fffffffffff3e57ffffffffffedd3800000000004000800000000000000],
    [0x7fffffffffff9ad7fffffffffff8c67ffffffffffca24800000000004000,
      0x7ffffffffffd4fb7ffffffffffd579800000000004000800000000000000],
    [0x7ffffffffffefed7fffffffffff7fe7ffffffffffef437fffffffffff76a7ffffffffffef68800000000004000,
      0x7fffffffffff2f37ffffffffffec8b7fffffffffff2257ffffffffffebac800000000004000800000000000000],
    [0x8000000000000008000000000000007ffffffffffdb997ffffffffffec9b7ffffffffffec9b800000000004000,
      0x8000000000000008000000000000007ffffffffffde807ffffffffffd173800000000004000800000000000000],
    [0x7fffffffffff3557fffffffffff1917ffffffffffcb15800000000004000,
      0x7ffffffffffb1467ffffffffffb23e800000000004000800000000000000],
    [0x7ffffffffffc2cd800000000004000,
      0x800000000004000800000000000000]] : List (List ℕ)).getD ξ []).getD i 0

/-- The weight of column `k` of the factor of node `ξ`. -/
def weights (ξ k : ℕ) : ℕ :=
  (([[82432, 77086],
    [89408, 83699],
    [81600, 23808],
    [141696, 132172],
    [27456, 24935],
    [67264, 21279],
    [73088, 6260]] : List (List ℕ)).getD ξ []).getD k 0

/-- The tree: its shape, the sizes of the check and its rows. -/
def tree : FrontTree where
  nodes := 7
  parent := fun ξ ↦ [2, 2, 6, 5, 5, 6, 0].getD ξ 0
  kids := fun ξ ↦ [[], [], [0, 1], [], [], [3, 4], [2, 5]].getD ξ []
  rank := fun ξ ↦ [2, 2, 2, 2, 2, 2, 2].getD ξ 0
  size := fun ξ ↦ [6, 6, 4, 6, 6, 4, 2].getD ξ 0
  width := 60
  leafBits := 15
  schurBits := 16
  matrixBits := 18
  factorBits := 17
  residualBits := 35
  scale := 17179869184
  lift := fun _ ↦ 29
  penalty := fun ξ ↦ [6, 6, 4, 6, 6, 4, 2].getD ξ 0
  diagonalBound := 2097152
  leaf := leafRows
  schur := schurRows
  factor := factorCols
  weight := weights

/-- Column `i` of node `ξ`, as a packed row of biased slots on the chain of the node. -/
def colRows (ξ i : ℕ) : ℕ :=
  (([[],
    [],
    [],
    [],
    [],
    [],
    [0x7ffffffffffffeb7ffffffffffffeb]] : List (List ℕ)).getD ξ []).getD i 0

/-- The columns: their number at each node, their rows, and the bit bounds of the column
entries and of the leaf entries. -/
def cols : FrontTree.Cols where
  count := fun ξ ↦ [0, 0, 0, 0, 0, 0, 1].getD ξ 0
  col := colRows
  bits := 7
  leafBits := 15

/-- The idle mask of node `ξ`: all bits of a slot are set if the row of that slot is after
the pivots and no factor column of the node has an entry in it. -/
def idle (ξ : ℕ) : ℕ :=
  ([0xffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x0,
    0xffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000,
    0x0,
    0x0] : List ℕ).getD ξ 0

/-- The unknown in slot `p` of the chain of node `ξ`: the pivots of `ξ` are numbered from
its first unknown, and the later slots are the chain of the parent. -/
def chain : ℕ → ℕ → ℕ → ℕ
  | 0, ξ, p => [0, 2, 4, 6, 8, 10, 12].getD ξ 0 + p
  | f + 1, ξ, p => if p < tree.rank ξ then [0, 2, 4, 6, 8, 10, 12].getD ξ 0 + p
      else chain f (tree.parent ξ) (p - tree.rank ξ)

/-- The test of every node that does not depend on a row passes. -/
theorem nodes_ok : ∀ ξ < tree.nodes, (tree.withCols cols).nodeCheck ξ = true := by decide +kernel

/-- The idle mask of every node marks rows without factor entries. -/
theorem idle_ok : ∀ ξ < tree.nodes, (tree.withCols cols).idleCheck idle ξ = true := by
  decide +kernel

/-- The tests of every row pass, with the cheap test for the 4 idle rows. -/
theorem fast_ok : ∀ ξ < tree.nodes, ∀ i < tree.size ξ,
    (tree.withCols cols).fastRowCheck idle ξ i = true := by
  decide +kernel

/-- The tests of every row of every node pass. -/
theorem rows_ok : ∀ ξ < tree.nodes, ∀ i < tree.size ξ,
    (tree.withCols cols).rowCheck ξ i = true :=
  fun ξ hξ i hi ↦
    (tree.withCols cols).rowCheck_of_fast idle (idle_ok ξ hξ) hi (fast_ok ξ hξ i hi)

/-- The tests of the columns of every node pass. -/
theorem cols_ok : ∀ ξ < tree.nodes, tree.colsCheck cols ξ = true := by decide +kernel

/-- The entry bound of every leaf row holds. -/
theorem leaves_ok : ∀ ξ < tree.nodes, ∀ i < tree.size ξ,
    tree.colsRowCheck cols ξ i = true := by
  decide +kernel

/-- Without the columns these rows and this factor fail the row tests. This is a statement
about these data, not about every factor. -/
theorem rows_fail : ¬ ∀ ξ < tree.nodes, ∀ i < tree.size ξ, tree.rowCheck ξ i = true := by
  decide +kernel

/-- The chains agree along the tree. -/
theorem chain_ok : ∀ ξ < tree.nodes, ξ + 1 < tree.nodes → ∀ p < tree.size (tree.parent ξ),
    chain 2 ξ (p + tree.rank ξ) = chain 2 (tree.parent ξ) p := by decide +kernel

/-- The margin of every node is at least `23`. -/
theorem gain_ok : ∀ ξ < tree.nodes,
    tree.scale * 23 + tree.size ξ * slotBias tree.residualBits ≤
      tree.scale * tree.lift ξ := by
  decide +kernel

/-- **The assembled form plus the squares of the columns is positive definite**: for every
real vector of the 14 unknowns, `23` times the sum of the squares of the pivots of all nodes
is at most the sum of the leaf forms plus the squares of the columns applied to the vector.
One invented example; the factor and the columns came from a GPU and only this bound is
proved. -/
theorem assembled_ge (x : ℕ → ℝ) :
    (23 : ℕ) * ∑ ξ ∈ Finset.range tree.nodes, ∑ p ∈ Finset.range (tree.rank ξ),
        x (chain 2 ξ p) ^ 2 ≤
      ∑ ξ ∈ Finset.range tree.nodes, tree.leafForm ξ (fun p ↦ x (chain 2 ξ p)) +
        ∑ ξ ∈ Finset.range tree.nodes, tree.colForm cols ξ (fun p ↦ x (chain 2 ξ p)) :=
  tree.uniform_le_global_cols cols (by decide) nodes_ok rows_ok cols_ok leaves_ok (chain 2)
    (fun ξ hξ p hp ↦ chain_ok ξ (by omega) hξ p hp) gain_ok x

/-! ### The same witnesses, computed during elaboration -/

/-- The entries of the leaf matrix of node `ξ` on and above its diagonal: triples (row, column,
value) on the chain of the node, one after the other. -/
def entries (ξ : ℕ) : List ℤ :=
  ([[0, 0, 1317, 0, 1, -328, 0, 2, -328, 0, 3, -657, 1, 1, 1317, 1, 2, -657, 1, 3, -328, 2, 2,
     1317, 2, 3, -328, 3, 3, 1317],
    [0, 0, 1426, 0, 1, -353, 0, 2, -164, 0, 3, -330, 0, 4, -189, 0, 5, -380, 1, 1, 1426, 1, 2,
     -330, 1, 3, -164, 1, 4, -380, 1, 5, -189, 2, 2, 663, 2, 3, -164, 3, 3, 663, 4, 4, 763, 4, 5,
     -189, 5, 5, 763],
    [0, 0, 0],
    [0, 0, 2243, 0, 1, -574, 0, 2, -297, 0, 3, -579, 0, 4, -277, 0, 5, -556, 1, 1, 2243, 1, 2,
     -579, 1, 3, -297, 1, 4, -556, 1, 5, -277, 2, 2, 1128, 2, 3, -297, 3, 3, 1128, 4, 4, 1115, 4,
     5, -277, 5, 5, 1115],
    [0, 0, 458, 0, 1, -130, 0, 2, -130, 0, 3, -244, 1, 1, 458, 1, 2, -244, 1, 3, -130, 2, 2, 458,
     2, 3, -130, 3, 3, 458],
    [0, 0, 0],
    [0, 0, 0]] : List (List ℤ)).getD ξ []

/-- The tables that `FrontTree.solveTree` computes from `entries` and the columns: for node
`ξ`, at the index `5 ξ` its leaf rows, at `5 ξ + 1` the rows after its pivots of the matrix
that it passes up, at `5 ξ + 2` its factor columns, at `5 ξ + 3` its packed weights and at
`5 ξ + 4` its idle mask. -/
def solvedTables : Array (Array ℕ) :=
  FrontTree.solveTree tree cols 14 fun ξ ↦
    FrontTree.sparseRows 60 (tree.size ξ)
      (biasedPack 64 (entries ξ).length fun k ↦ (entries ξ).getD k 0) ((entries ξ).length / 3)

/-- The entries of `solvedTables` as literals: compiled code evaluates `solvedTables` once
while this module is compiled, and `solved j i` is the literal of its entry `i` of table `j`. -/
def solved : ℕ → ℕ → ℕ := computed_tables% solvedTables

/-- The tree with the computed tables in place of the stored ones. -/
def solvedTree : FrontTree :=
  { tree with
    leaf := fun ξ ↦ solved (Nat.mul 5 ξ)
    schur := fun ξ i ↦ solved (Nat.add (Nat.mul 5 ξ) 1) (Nat.sub i (tree.rank ξ))
    factor := fun ξ ↦ solved (Nat.add (Nat.mul 5 ξ) 2)
    weight := fun ξ k ↦ slot 64 k (solved (Nat.add (Nat.mul 5 ξ) 3) 0) }

/-- The computed idle mask of node `ξ`. -/
def solvedIdle (ξ : ℕ) : ℕ := solved (Nat.add (Nat.mul 5 ξ) 4) 0

/-- The leaf rows expanded from the triples of the entries are the stored leaf rows. -/
theorem solved_leaf : ∀ ξ < tree.nodes, ∀ i < tree.size ξ,
    solvedTree.leaf ξ i = tree.leaf ξ i := by
  decide +kernel

/-- The computed tables pass the tests of every node and of every row: the test of the node,
the test of the computed idle mask, and the row tests with the cheap test for the idle rows.
These are the hypotheses of `FrontTree.uniform_le_global_cols` on the factor (the row tests
through `FrontTree.rowCheck_of_fast`); its other hypotheses read the leaf rows, the columns
and the shape, which `solvedTree` shares with `tree`. One invented example. -/
theorem solved_ok : ∀ ξ < tree.nodes,
    (solvedTree.withCols cols).nodeCheck ξ = true ∧
      (solvedTree.withCols cols).idleCheck solvedIdle ξ = true ∧
      ∀ i < tree.size ξ, (solvedTree.withCols cols).fastRowCheck solvedIdle ξ i = true := by
  decide +kernel

/-- `computed_tables%` refuses a term without tables. -/
example : True := by
  fail_if_success
    exact (fun _ : ℕ → ℕ → ℕ ↦ trivial) (computed_tables% (#[] : Array (Array ℕ)))
  trivial

end CAS.Examples.Numerics.FrontTree

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.LowRankLDL
public import CAS.Numerics.MatrixPositivity

/-!
# A tree of fronts: positivity of a sparse assembled matrix from packed `LDLᵀ` checks

## Motivation

A sparse symmetric matrix `N` is the sum of small matrices, each on the unknowns of one cell of
a mesh. Can the kernel prove `xᵀ N x ≥ ∑ γ_j x_j²` for every real `x` without ever storing or
forming a matrix on all the unknowns, and with work that follows the fill of a sparse
factorization? This is the question behind the tree of matrices in BlowupZoo's statement of the
unforced Navier-Stokes blowup (its condition `TreeConditionsGiven`), asked for data of our own.

## The idea

The unknowns are eliminated along a tree, as in a multifrontal factorization. Node `ξ`
eliminates its own unknowns, the `rank ξ` pivots, and its matrix (its front) also touches
unknowns that ancestors eliminate. We give every node the same simple layout: the slots of a row
of node `ξ` are its pivots, then the pivots of its parent, then those of its grandparent, up to
the root (the chain of `ξ`, of length `size ξ`). The chain of the parent is the chain of `ξ`
without its first `rank ξ` slots, so a row moves from a node to its parent by one shift.

The front of `ξ` is the sum of its own leaf matrix and of the matrices `S_c` that its children
pass up. An untrusted program (a GPU) computes a partial factorization of the front: `rank ξ`
columns of a factor `L` with weights `d`, and an integer matrix `S_ξ` on the slots after the
pivots, close to the Schur complement. The kernel checks one identity per row of each front,
with the packed row test of [PackedLDL](PackedLDL.lean):
`a (front - (0 ⊕ S)) - a β (I_pivots ⊕ 0) = L D Lᵀ + R` with every entry of `R` at most `ε`.
Since `L D Lᵀ` is nonnegative, this gives, for every real vector `y` on the chain,
`front(y) ≥ γ |y_pivots|² + S(y_rest) - P |y_rest|²` with `γ = β - (size) ε / a` and any
`P ≥ (size) ε / a`. The form `S - P` is what the parent receives. Adding these inequalities over
the nodes, every passed form occurs once on each side and cancels, and the root passes nothing.

## Main results

The inequalities assume a positive multiplier `scale`.

* `FrontTree.node_ge` (all trees, all nodes): the inequality of one node, from its row checks
  and the guards of its children's passed rows.
* `FrontTree.sum_gain_le` (all trees): if the checks of every node pass, then for every family
  `y ξ` of chain vectors that agree along the tree,
  `∑ ξ, gain ξ * |pivots of y ξ|² ≤ ∑ ξ, leafForm ξ (y ξ)`.
* `FrontTree.sum_gain_le_global` (all trees): the same for one vector `x` of all the unknowns
  and a numbering `chain ξ p` of the chain slots: the assembled form
  `∑ ξ, leafForm ξ (x ∘ chain ξ)` is at least `∑ ξ, gain ξ * ∑ p < rank ξ, x (chain ξ p)²`.
* `FrontTree.uniform_le_global` (all trees): the same with one natural number `g` below every
  margin, `g * ∑ ξ, ∑ p < rank ξ, x (chain ξ p)² ≤ ∑ ξ, leafForm ξ (x ∘ chain ξ)`.
* `FrontTree.uniform_le_global_cols` (all trees, all columns): the same bound with the squares
  of finitely many columns per node added on the right, for an assembled matrix with negative
  directions. The check runs on the leaves plus the outer products of the columns.
* `FrontTree.rowCheck_of_fast` (all trees, all masks): a row after the pivots of a node in
  which no factor column has an entry passes `rowCheck` if it passes the cheap test
  `fastRowCheck`, whose residual row combines two rows instead of one per pivot. The rows are
  marked by a mask per node, tested once per factor column (`idleCheck`).

## Relations

Each node is one use of `quadForm_ge_of_ldltRowCheck` ([PackedLDL](PackedLDL.lean)), applied to
the assembled row `asmRow`, which is one `packedRowCombination`
([PackedLinearAlgebra](PackedLinearAlgebra.lean)). A tree with one node and no passed matrix is
that theorem itself: `FrontTree.sum_gain_le` generalizes it from a dense matrix to a sum of
matrices along a tree. In BlowupZoo's statement the passed forms are existential witnesses; here
they are data that the checker reads.

The columns are a positive term of low rank: `colsRow` is `lowRankRow`
([LowRankLDL](LowRankLDL.lean)) for the negated leaf row, and `uniform_le_global_cols` is
`uniform_le_global` at `T.withCols C`. `rowCheck_of_fast` rests on `ldltResidualRow_eq_idle`:
the residual row of [PackedLDL](PackedLDL.lean) for a row without factor entries is
`idleResidualRow`.

## Scope

Every chain slot of a node is a row of its check, also for unknowns that the front does not
touch. Such a row is cheap with `fastRowCheck`, but it still has the length of the chain, and
its leaf row, passed rows and assembled row are still formed; a layout with one row list per
node would drop it. The matrices passed up are stored, not recomputed. The columns are data of
the certificate; nothing finds them.
-/

@[expose] public section

open Finset

namespace CAS.Numerics

/-! ### Quadratic forms on an initial segment -/

/-- The form `∑ i < n, ∑ j < n, M i j * y i * y j` of the matrix `M` on the first `n` slots. -/
def rangeForm (n : ℕ) (M : ℕ → ℕ → ℝ) (y : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range n, ∑ j ∈ range n, M i j * y i * y j

/-- The sum of squares `∑ i < n, y i ^ 2`. -/
def rangeSq (n : ℕ) (y : ℕ → ℝ) : ℝ := ∑ i ∈ range n, y i ^ 2

/-- The form depends only on the entries with both indices below `n`. -/
theorem rangeForm_congr {n : ℕ} {M M' : ℕ → ℕ → ℝ} (h : ∀ i < n, ∀ j < n, M i j = M' i j)
    (y : ℕ → ℝ) : rangeForm n M y = rangeForm n M' y :=
  sum_congr rfl fun i hi ↦ sum_congr rfl fun j hj ↦ by
    rw [h i (mem_range.mp hi) j (mem_range.mp hj)]

/-- The form depends only on the first `n` entries of the vector. -/
theorem rangeForm_congr_vec {n : ℕ} (M : ℕ → ℕ → ℝ) {y y' : ℕ → ℝ} (h : ∀ i < n, y i = y' i) :
    rangeForm n M y = rangeForm n M y' :=
  sum_congr rfl fun i hi ↦ sum_congr rfl fun j hj ↦ by
    rw [h i (mem_range.mp hi), h j (mem_range.mp hj)]

/-- The sum of squares depends only on the first `n` entries of the vector. -/
theorem rangeSq_congr {n : ℕ} {y y' : ℕ → ℝ} (h : ∀ i < n, y i = y' i) :
    rangeSq n y = rangeSq n y' :=
  sum_congr rfl fun i hi ↦ by rw [h i (mem_range.mp hi)]

/-- The form is additive in the matrix. -/
theorem rangeForm_add (n : ℕ) (M M' : ℕ → ℕ → ℝ) (y : ℕ → ℝ) :
    rangeForm n (fun i j ↦ M i j + M' i j) y = rangeForm n M y + rangeForm n M' y := by
  simp only [rangeForm, add_mul, sum_add_distrib]

/-- The form of a difference of matrices is the difference of their forms. -/
theorem rangeForm_sub (n : ℕ) (M M' : ℕ → ℕ → ℝ) (y : ℕ → ℝ) :
    rangeForm n (fun i j ↦ M i j - M' i j) y = rangeForm n M y - rangeForm n M' y := by
  simp only [rangeForm, sub_mul, sum_sub_distrib]

/-- The form of a sum of matrices over a list is the sum of their forms. -/
theorem rangeForm_list_sum {ι : Type*} (n : ℕ) (l : List ι) (M : ι → ℕ → ℕ → ℝ) (y : ℕ → ℝ) :
    rangeForm n (fun i j ↦ (l.map fun c ↦ M c i j).sum) y =
      (l.map fun c ↦ rangeForm n (M c) y).sum := by
  induction l with
  | nil => simp [rangeForm]
  | cons c l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [rangeForm_add, ih]

/-- The form of a diagonal matrix is the weighted sum of squares. -/
theorem rangeForm_diag (n : ℕ) (d : ℕ → ℝ) (y : ℕ → ℝ) :
    rangeForm n (fun i j ↦ if j = i then d i else 0) y = ∑ i ∈ range n, d i * y i ^ 2 := by
  refine sum_congr rfl fun i hi ↦ ?_
  simp only [ite_mul, zero_mul]
  rw [sum_ite_eq' (range n) i, ite_eq_left hi]
  ring

/-- A matrix that vanishes unless both indices are at least `r` has the form of its lower right
block, on the vector moved by `r`. -/
theorem rangeForm_shift {r m : ℕ} {M : ℕ → ℕ → ℝ}
    (hrow : ∀ i < r, ∀ j, M i j = 0) (hcol : ∀ i, ∀ j < r, M i j = 0) (y : ℕ → ℝ) :
    rangeForm (r + m) M y =
      rangeForm m (fun i j ↦ M (i + r) (j + r)) (fun p ↦ y (p + r)) := by
  unfold rangeForm
  rw [sum_range_add, sum_eq_zero fun i hi ↦ sum_eq_zero fun j _ ↦ by
    rw [hrow i (mem_range.mp hi) j, zero_mul, zero_mul], zero_add]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [sum_range_add, sum_eq_zero fun j hj ↦ by
    rw [hcol (r + i) j (mem_range.mp hj), zero_mul, zero_mul], zero_add]
  exact sum_congr rfl fun j _ ↦ by rw [Nat.add_comm r i, Nat.add_comm r j]

/-- The sum of squares on `r + m` slots splits at `r`. -/
theorem rangeSq_add (r m : ℕ) (y : ℕ → ℝ) :
    rangeSq (r + m) y = rangeSq r y + rangeSq m (fun p ↦ y (p + r)) := by
  unfold rangeSq
  rw [sum_range_add]
  exact congrArg _ (sum_congr rfl fun i _ ↦ by rw [Nat.add_comm r i])

/-- A sum over the positions of a list is the sum of the list. -/
theorem sum_range_getD {M : Type*} [AddCommMonoid M] (l : List ℕ) (g : ℕ → M) :
    ∑ j ∈ range l.length, g (l.getD j 0) = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [List.length_cons, sum_range_succ', List.map_cons, List.sum_cons, add_comm]
    exact congrArg _ (by simpa using ih)

/-- The real value of an integer sum over a list is the sum of the real values. -/
theorem cast_list_sum_map (l : List ℕ) (f : ℕ → ℤ) :
    (((l.map f).sum : ℤ) : ℝ) = (l.map fun c ↦ (f c : ℝ)).sum := by
  induction l with
  | nil => simp
  | cons c l ih => simp [ih]

/-- Signed slots of the bias row vanish. -/
theorem signedSlot_biasRow {w n k : ℕ} (hk : k < n) : signedSlot w k (biasRow w n) = 0 := by
  rw [signedSlot, biasRow_eq_packSlots, slot_packed_eq (fun _ _ ↦ slotBias_lt w),
    ite_eq_left hk, sub_self]

/-- The bias row is a packed row of `n` slots. -/
theorem biasRow_lt (w n : ℕ) : biasRow w n < 2 ^ (w * n) := by
  rw [biasRow_eq_packSlots]
  exact packSlots_lt fun _ _ ↦ slotBias_lt w

/-- Slot `k` of a row moved down by `m` slots is slot `k + m` of the row. -/
theorem signedSlot_shiftRight (w m k x : ℕ) :
    signedSlot w k (Nat.shiftRight x (Nat.mul w m)) = signedSlot w (k + m) x := by
  change signedSlot w k (x >>> (w * m)) = _
  rw [signedSlot, signedSlot, Nat.shiftRight_eq_div_pow, slot_div_two_pow]

/-- A row of `m + n` slots moved down by `m` slots is a row of `n` slots. -/
theorem shiftRight_lt {w m n x : ℕ} (hx : x < 2 ^ (w * (m + n))) :
    Nat.shiftRight x (Nat.mul w m) < 2 ^ (w * n) := by
  change x >>> (w * m) < _
  rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
  rwa [Nat.mul_add, Nat.add_comm] at hx

/-- The form of a sum of outer products is the sum of the squares of the columns applied to the
vector: `quadForm_ldlt_eq` with unit weights, on initial segments. -/
theorem rangeForm_sum_outer (n m : ℕ) (u : ℕ → ℕ → ℝ) (y : ℕ → ℝ) :
    rangeForm n (fun i j ↦ ∑ c ∈ range m, u c i * u c j) y =
      ∑ c ∈ range m, (∑ i ∈ range n, u c i * y i) ^ 2 := by
  simp only [rangeForm, Finset.sum_range]
  simpa only [mul_one, one_mul] using CAS.Analysis.Matrix.quadForm_ldlt_eq
    (fun (i : Fin n) (c : Fin m) ↦ u c i) (fun _ ↦ 1) fun i ↦ y i

/-! ### Negated rows -/

/-- The bias of a narrower slot is smaller. -/
theorem slotBias_lt_slotBias {g w : ℕ} (h : g < w) : slotBias g < slotBias w := by
  rw [slotBias_eq, slotBias_eq]
  have h1 : 2 ^ g / 2 < 2 ^ g := Nat.div_lt_self (Nat.two_pow_pos g) one_lt_two
  have h2 : 2 ^ g ≤ 2 ^ w / 2 := by
    rw [Nat.le_div_iff_mul_le two_pos, ← pow_succ]
    exact Nat.pow_le_pow_right two_pos h
  omega

/-- A passing guard with `g < w` makes every slot positive. -/
theorem slot_pos_of_signedGuardCheck {w g n x k : ℕ} (hg : g < w)
    (h : signedGuardCheck w g n x = true) (hk : k < n) : 0 < slot w k x := by
  have h1 := natAbs_signedSlot_le_of_signedGuardCheck hg h hk
  have h2 := slotBias_lt_slotBias hg
  rw [signedSlot] at h1
  omega

/-- Twice the bias of a slot of positive width is `2 ^ w`. -/
theorem slotBias_add_self {w : ℕ} (hw : 0 < w) : slotBias w + slotBias w = 2 ^ w := by
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
  rw [slotBias_succ, pow_succ]
  omega

/-- The packed row of the negated entries of `x`: twice the bias row minus `x`. -/
def negRow (w n x : ℕ) : ℕ := Nat.sub (Nat.add (biasRow w n) (biasRow w n)) x

/-- The negated row packs the slots `2 ^ w - slot w k x`. -/
theorem negRow_eq_packSlots {w n x : ℕ} (hw : 0 < w) (hx : x < 2 ^ (w * n)) :
    negRow w n x = packSlots w n fun k ↦ 2 ^ w - slot w k x := by
  have h2 : biasRow w n + biasRow w n = packSlots w n fun _ ↦ 2 ^ w := by
    rw [biasRow_eq_packSlots, packSlots_add]
    simp only [slotBias_add_self hw]
  have hsum : packSlots w n (fun k ↦ 2 ^ w - slot w k x) + packSlots w n (fun k ↦ slot w k x) =
      packSlots w n fun _ ↦ 2 ^ w := by
    rw [packSlots_add, packSlots_eq_sum, packSlots_eq_sum]
    exact sum_congr rfl fun k _ ↦ by rw [Nat.sub_add_cancel (slot_lt w k x).le]
  rw [packSlots_slot hx] at hsum
  change biasRow w n + biasRow w n - x = _
  rw [h2, ← hsum, Nat.add_sub_cancel]

/-- A negated row with positive slots is a packed row of `n` slots. -/
theorem negRow_lt {w n x : ℕ} (hw : 0 < w) (hx : x < 2 ^ (w * n))
    (hpos : ∀ j < n, 0 < slot w j x) : negRow w n x < 2 ^ (w * n) := by
  rw [negRow_eq_packSlots hw hx]
  exact packSlots_lt fun j hj ↦ Nat.sub_lt (Nat.two_pow_pos w) (hpos j hj)

/-- The signed slots of a negated row with positive slots are the negated signed slots. -/
theorem signedSlot_negRow {w n x k : ℕ} (hw : 0 < w) (hx : x < 2 ^ (w * n))
    (hpos : ∀ j < n, 0 < slot w j x) (hk : k < n) :
    signedSlot w k (negRow w n x) = -signedSlot w k x := by
  have hb := slotBias_add_self hw
  rw [negRow_eq_packSlots hw hx, signedSlot, signedSlot,
    slot_packed_eq (fun j hj ↦ Nat.sub_lt (Nat.two_pow_pos w) (hpos j hj)), ite_eq_left hk]
  have hs := slot_lt w k x
  omega

/-! ### Rows without factor entries -/

/-- A slot of a bitwise conjunction is the conjunction of the slots. -/
theorem slot_land (w k x y : ℕ) :
    slot w k (Nat.land x y) = Nat.land (slot w k x) (slot w k y) := by
  refine Nat.eq_of_testBit_eq fun i ↦ ?_
  change (slot w k (x &&& y)).testBit i = (slot w k x &&& slot w k y).testBit i
  rw [Nat.testBit_and, testBit_slot, testBit_slot, testBit_slot, Nat.testBit_and]
  cases decide (i < w) <;> simp

/-- If two numbers agree on a mask whose slot `k` is all ones, their slots `k` are equal. -/
theorem slot_eq_of_land_eq {w k x y M : ℕ} (hM : slot w k M = slotMask w)
    (h : Nat.land x M = Nat.land y M) : slot w k x = slot w k y := by
  have hself : ∀ z, Nat.land (slot w k z) (slotMask w) = slot w k z := fun z ↦ by
    change slot w k z &&& slotMask w = _
    rw [slotMask_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (slot_lt w k z)]
  rw [← hself x, ← hself y, ← hM, ← slot_land, ← slot_land, h]

/-- The residual row of a row all of whose factor entries are zero: `a M i - b e i`, a
combination of two rows instead of one per factor column. -/
def idleResidualRow (p : PackedLDLParams) (Mrow : ℕ → ℕ) (i : ℕ) : ℕ :=
  packedRowCombination p.width p.size 2 p.offset
    (fun j ↦ cond (Nat.beq j 0) (Nat.add p.offset p.scale) (Nat.sub p.offset p.shift))
    (fun j ↦ cond (Nat.beq j 0) (Mrow i) (unitRow p.width p.size i))

/-- Adding `α * X + m * α * β` to both terms of a truncated subtraction does not change it. This
removes the factor columns from the residual row in `ldltResidualRow_eq_idle`. -/
private theorem idle_arith (X M u β α a b m : ℕ) :
    (α * X + a * M + b * u + ((m + 2) * α + 1) * β) - (α * (X + M + u) + (m * α + a + b) * β) =
      (0 + a * M + b * u + (2 * α + 1) * β) - (α * (0 + M + u) + (0 + a + b) * β) := by
  have hA : α * X + a * M + b * u + ((m + 2) * α + 1) * β =
      (0 + a * M + b * u + (2 * α + 1) * β) + (α * X + m * α * β) := by ring
  have hB : α * (X + M + u) + (m * α + a + b) * β =
      (α * (0 + M + u) + (0 + a + b) * β) + (α * X + m * α * β) := by ring
  rw [hA, hB, Nat.add_sub_add_right]

/-- **A row without factor entries has the cheap residual row.** If slot `i` of every factor
column that row `i` uses is a zero entry, the residual row of the `LDLᵀ` check of row `i` is
`idleResidualRow`: the factor columns enter with coefficient zero and cancel. -/
theorem ldltResidualRow_eq_idle {p : PackedLDLParams} {Mrow Urow d : ℕ → ℕ} {i : ℕ}
    (hzero : ∀ j < p.columns i, slot p.width i (Urow j) = slotBias p.width) :
    ldltResidualRow p Mrow Urow d i = idleResidualRow p Mrow i := by
  set m := p.columns i with hm
  have hcoef : ∀ j < m, ldltCoefficient p Urow d i m j = p.offset := fun j hj ↦ by
    simp only [ldltCoefficient, Nat.blt_eq.mpr hj, Bool.cond_true, hzero j hj, Nat.add_eq,
      Nat.mul_eq, Nat.sub_eq]
    exact Nat.add_sub_cancel _ _
  have hrow : ∀ j < m, ldltRow p Mrow Urow i m j = Urow j := fun j hj ↦ by
    simp only [ldltRow, Nat.blt_eq.mpr hj, Bool.cond_true]
  have hmm : Nat.blt m m = false := by simp [Bool.eq_false_iff]
  have hm1 : Nat.blt (m + 1) m = false := by simp [Bool.eq_false_iff]
  have hm2 : Nat.beq (m + 1) m = false := by simp [Bool.eq_false_iff]
  have hcm : ldltCoefficient p Urow d i m m = p.offset + p.scale := by
    simp only [ldltCoefficient, hmm, Bool.cond_false, Nat.beq_refl, Bool.cond_true, Nat.add_eq]
  have hcm1 : ldltCoefficient p Urow d i m (m + 1) = p.offset - p.shift := by
    simp only [ldltCoefficient, hm1, hm2, Bool.cond_false, Nat.sub_eq]
  have hrm : ldltRow p Mrow Urow i m m = Mrow i := by
    simp only [ldltRow, hmm, Bool.cond_false, Nat.beq_refl, Bool.cond_true]
  have hrm1 : ldltRow p Mrow Urow i m (m + 1) = unitRow p.width p.size i := by
    simp only [ldltRow, hm1, hm2, Bool.cond_false]
  have hs1 : natSum m (fun j ↦ ldltCoefficient p Urow d i m j * ldltRow p Mrow Urow i m j) =
      p.offset * natSum m Urow := by
    rw [natSum_eq_sum, natSum_eq_sum, Finset.mul_sum]
    exact sum_congr rfl fun j hj ↦ by rw [hcoef j (mem_range.mp hj), hrow j (mem_range.mp hj)]
  have hs2 : natSum m (ldltRow p Mrow Urow i m) = natSum m Urow := by
    rw [natSum_eq_sum, natSum_eq_sum]
    exact sum_congr rfl fun j hj ↦ hrow j (mem_range.mp hj)
  have hs3 : natSum m (ldltCoefficient p Urow d i m) = m * p.offset := by
    rw [natSum_eq_sum, sum_congr rfl fun j hj ↦ hcoef j (mem_range.mp hj), sum_const, card_range,
      smul_eq_mul]
  unfold ldltResidualRow idleResidualRow packedRowCombination
  simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq, ← hm]
  rw [natSum_succ, natSum_succ, natSum_succ, natSum_succ, natSum_succ, natSum_succ, hs1, hs2, hs3,
    hcm, hcm1, hrm, hrm1]
  exact idle_arith _ _ _ _ _ _ _ _

/-! ### The tree -/

/-- A tree of fronts in chain layout. The nodes are `0, …, nodes - 1`, every node before its
parent, the root last. A row of node `ξ` has `size ξ` slots of `width` bits: the `rank ξ` pivots
of `ξ`, then the chain of its parent. The data are packed rows of biased slots: the leaf matrix
`leaf ξ i`, the matrix `schur ξ i` that `ξ` passes up (rows `i ≥ rank ξ`, zero in the pivot
slots), the factor columns `factor ξ k` and their weights `weight ξ k`. -/
structure FrontTree where
  /-- The number of nodes. -/
  nodes : ℕ
  /-- The parent of a node; not used at the root. -/
  parent : ℕ → ℕ
  /-- The children of a node, as the checker reads them. -/
  kids : ℕ → List ℕ
  /-- The number of pivots of a node. -/
  rank : ℕ → ℕ
  /-- The number of chain slots of a node. -/
  size : ℕ → ℕ
  /-- The slot width, in bits. -/
  width : ℕ
  /-- Leaf entries are at most `slotBias leafBits` in absolute value. -/
  leafBits : ℕ
  /-- Passed entries are at most `slotBias schurBits` in absolute value. -/
  schurBits : ℕ
  /-- Front entries are at most `slotBias matrixBits` in absolute value. -/
  matrixBits : ℕ
  /-- Factor entries are at most `slotBias factorBits` in absolute value. -/
  factorBits : ℕ
  /-- Residual entries are at most `ε = slotBias residualBits` in absolute value. -/
  residualBits : ℕ
  /-- The multiplier `a` of the fronts. -/
  scale : ℕ
  /-- The margin `β` of the pivots of a node, in units of the leaf entries. -/
  lift : ℕ → ℕ
  /-- The amount `P` taken from the diagonal of the matrix that a node passes up. -/
  penalty : ℕ → ℕ
  /-- A bound for the weights. -/
  diagonalBound : ℕ
  /-- Row `i` of the leaf matrix of a node. -/
  leaf : ℕ → ℕ → ℕ
  /-- Row `i ≥ rank ξ` of the matrix that node `ξ` passes up, in the layout of `ξ`. -/
  schur : ℕ → ℕ → ℕ
  /-- Column `k` of the factor of a node. -/
  factor : ℕ → ℕ → ℕ
  /-- The weight of column `k` of the factor of a node. -/
  weight : ℕ → ℕ → ℕ

namespace FrontTree

variable (T : FrontTree)

/-- The sizes of the packed `LDLᵀ` check of node `ξ`; its shift is `scale * lift ξ`. -/
def params (ξ : ℕ) : PackedLDLParams where
  width := T.width
  size := T.size ξ
  rank := T.rank ξ
  matrixBits := T.matrixBits
  factorBits := T.factorBits
  residualBits := T.residualBits
  scale := T.scale
  shift := Nat.mul T.scale (T.lift ξ)
  diagonalBound := T.diagonalBound

/-- The sum of the penalties of the children of `ξ`. -/
def kidPenalty (ξ : ℕ) : ℕ := ((T.kids ξ).map T.penalty).sum

/-- Row `i` of the matrix `0 ⊕ S_ξ` in the layout of `ξ`: the bias row for a pivot row. -/
def schurRow (ξ i : ℕ) : ℕ :=
  cond (Nat.blt i (T.rank ξ)) (biasRow T.width (T.size ξ)) (T.schur ξ i)

/-- Row `i` of the matrix that the child `c` passes up, in the layout of its parent. -/
def childRow (c i : ℕ) : ℕ :=
  Nat.shiftRight (T.schur c (Nat.add i (T.rank c))) (Nat.mul T.width (T.rank c))

/-- The rows combined for row `i` of the front of `ξ`: the leaf row, the rows of the children,
the row of `0 ⊕ S_ξ`, the unit row. -/
def asmRows (ξ i j : ℕ) : ℕ :=
  cond (Nat.beq j 0) (T.leaf ξ i)
    (cond (Nat.ble j (T.kids ξ).length) (T.childRow ((T.kids ξ).getD (Nat.sub j 1) 0) i)
      (cond (Nat.beq j (Nat.add (T.kids ξ).length 1)) (T.schurRow ξ i)
        (unitRow T.width (T.size ξ) i)))

/-- The coefficients of `asmRows`, with the offset `kidPenalty ξ + 1`: `1` for the leaf row and
the rows of the children, `-1` for `0 ⊕ S_ξ`, and `lift ξ` (on the rows after the pivots) minus
`kidPenalty ξ` for the unit row. -/
def asmCoef (ξ i j : ℕ) : ℕ :=
  cond (Nat.ble j (T.kids ξ).length) (Nat.add (T.kidPenalty ξ) 2)
    (cond (Nat.beq j (Nat.add (T.kids ξ).length 1)) (T.kidPenalty ξ)
      (cond (Nat.ble (T.rank ξ) i) (Nat.add (T.lift ξ) 1) 1))

/-- Row `i` of the matrix that node `ξ` hands to the packed `LDLᵀ` check:
`leaf + ∑ children (S_c - P_c I) - (0 ⊕ S_ξ) + lift (0 ⊕ I)`. -/
def asmRow (ξ i : ℕ) : ℕ :=
  packedRowCombination T.width (T.size ξ) (Nat.add (T.kids ξ).length 3)
    (Nat.add (T.kidPenalty ξ) 1) (T.asmCoef ξ i) (T.asmRows ξ i)

/-- The bound of the entries of an assembled row:
`slotBias leafBits + (kids + 1) slotBias schurBits + lift + kidPenalty`. -/
def asmBound (ξ : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.add (slotBias T.leafBits)
    (Nat.mul (Nat.add (T.kids ξ).length 1) (slotBias T.schurBits))) (T.lift ξ)) (T.kidPenalty ξ)

/-- The test of node `ξ` that does not depend on a row: the sizes of its `LDLᵀ` check fit, the
bit bounds are below the width, the assembled entries fit a slot, the penalty covers the
residual (`size * ε ≤ scale * penalty`), the list of children is the list of the earlier nodes
with parent `ξ`, and the chain of `ξ` is its pivots followed by the chain of its parent (for the
root: its pivots). -/
def nodeCheck (ξ : ℕ) : Bool :=
  (T.params ξ).valid && Nat.blt T.leafBits T.width && Nat.blt T.schurBits T.width &&
    Nat.blt (Nat.mul 2 (T.asmBound ξ)) (Nat.shiftLeft 1 T.width) &&
    Nat.ble (Nat.mul (T.size ξ) (slotBias T.residualBits)) (Nat.mul T.scale (T.penalty ξ)) &&
    decide (T.kids ξ = (List.range ξ).filter fun c ↦ Nat.beq (T.parent c) ξ) &&
    cond (Nat.blt (Nat.add ξ 1) T.nodes)
      (Nat.blt ξ (T.parent ξ) && Nat.blt (T.parent ξ) T.nodes &&
        Nat.beq (T.size ξ) (Nat.add (T.rank ξ) (T.size (T.parent ξ))))
      (Nat.beq (T.size ξ) (T.rank ξ))

/-- The test of row `i` of node `ξ`: the entry bound of the leaf row; for a row after the pivots
the entry bound of the passed row and its zero pivot slots; and the packed `LDLᵀ` row check of
the assembled front. -/
def rowCheck (ξ i : ℕ) : Bool :=
  signedGuardCheck T.width T.leafBits (T.size ξ) (T.leaf ξ i) &&
    cond (Nat.blt i (T.rank ξ)) true
      (signedGuardCheck T.width T.schurBits (T.size ξ) (T.schur ξ i) &&
        Nat.beq (Nat.land (T.schur ξ i) (slotMask (Nat.mul T.width (T.rank ξ))))
          (biasRow T.width (T.rank ξ))) &&
    ldltRowCheck (T.params ξ) (T.asmRow ξ) (T.factor ξ) (T.weight ξ) i

/-! ### The forms of the statement -/

/-- The leaf form of node `ξ` on a chain vector. -/
def leafForm (ξ : ℕ) (y : ℕ → ℝ) : ℝ :=
  rangeForm (T.size ξ) (fun i j ↦ (signedSlot T.width j (T.leaf ξ i) : ℝ)) y

/-- The entries of the matrix that `c` passes up, in the layout of its parent. -/
def passEntry (c i j : ℕ) : ℝ :=
  (signedSlot T.width (j + T.rank c) (T.schur c (i + T.rank c)) : ℝ)

/-- The form that node `c` passes to its parent, on a chain vector of the parent:
`S_c - penalty c`. -/
def pass (c : ℕ) (y : ℕ → ℝ) : ℝ :=
  rangeForm (T.size c - T.rank c) (T.passEntry c) y -
    T.penalty c * rangeSq (T.size c - T.rank c) y

/-- The margin of the pivots of node `ξ`: `lift ξ - size ξ * ε / scale`. -/
noncomputable def gain (ξ : ℕ) : ℝ :=
  ((T.scale : ℝ) * T.lift ξ - T.size ξ * slotBias T.residualBits) / T.scale

/-! ### What the tests give -/

/-- The parts of a passing `nodeCheck`. -/
theorem nodeCheck_spec {ξ : ℕ} (h : T.nodeCheck ξ = true) :
    (T.params ξ).valid = true ∧ T.leafBits < T.width ∧ T.schurBits < T.width ∧
      2 * T.asmBound ξ < 2 ^ T.width ∧
      T.size ξ * slotBias T.residualBits ≤ T.scale * T.penalty ξ ∧
      T.kids ξ = (List.range ξ).filter (fun c ↦ Nat.beq (T.parent c) ξ) ∧
      (ξ + 1 < T.nodes → ξ < T.parent ξ ∧ T.parent ξ < T.nodes ∧
        T.size ξ = T.rank ξ + T.size (T.parent ξ)) ∧
      (¬ ξ + 1 < T.nodes → T.size ξ = T.rank ξ) := by
  simp only [nodeCheck, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, h3, ?_, h5, h6, fun hlt ↦ ?_, fun hlt ↦ ?_⟩
  · change 2 * T.asmBound ξ < 1 <<< T.width at h4
    rwa [Nat.one_shiftLeft] at h4
  · have hlt' : Nat.blt (Nat.add ξ 1) T.nodes = true := Nat.blt_eq.mpr hlt
    rw [hlt'] at h7
    simp only [Bool.cond_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h7
    exact ⟨h7.1.1, h7.1.2, h7.2⟩
  · have hlt' : Nat.blt (Nat.add ξ 1) T.nodes = false := by
      rw [← Bool.not_eq_true, Nat.blt_eq]
      exact hlt
    rw [hlt'] at h7
    simpa only [Bool.cond_false, Nat.beq_eq] using h7

/-- A child of `ξ` in the checked list is an earlier node with parent `ξ`, and conversely. -/
theorem mem_kids_iff {ξ c : ℕ} (h : T.nodeCheck ξ = true) :
    c ∈ T.kids ξ ↔ c < ξ ∧ T.parent c = ξ := by
  rw [(T.nodeCheck_spec h).2.2.2.2.2.1]
  simp

/-- The parts of a passing `rowCheck`. -/
theorem rowCheck_spec {ξ i : ℕ} (h : T.rowCheck ξ i = true) :
    signedGuardCheck T.width T.leafBits (T.size ξ) (T.leaf ξ i) = true ∧
      (T.rank ξ ≤ i → signedGuardCheck T.width T.schurBits (T.size ξ) (T.schur ξ i) = true ∧
        Nat.land (T.schur ξ i) (slotMask (Nat.mul T.width (T.rank ξ))) =
          biasRow T.width (T.rank ξ)) ∧
      ldltRowCheck (T.params ξ) (T.asmRow ξ) (T.factor ξ) (T.weight ξ) i = true := by
  simp only [rowCheck, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun hi ↦ ?_, h3⟩
  have hlt : Nat.blt i (T.rank ξ) = false := by
    rw [← Bool.not_eq_true, Nat.blt_eq]
    omega
  rw [hlt] at h2
  simpa only [Bool.cond_false, Bool.and_eq_true, Nat.beq_eq] using h2

/-- The entries of a pivot row `i < rank ξ` of `0 ⊕ S_ξ` are zero. -/
theorem signedSlot_schurRow_of_lt {ξ i k : ℕ} (hk : k < T.size ξ) (hi : i < T.rank ξ) :
    signedSlot T.width k (T.schurRow ξ i) = 0 := by
  have hlt : Nat.blt i (T.rank ξ) = true := Nat.blt_eq.mpr hi
  rw [schurRow, hlt, Bool.cond_true, signedSlot_biasRow hk]

/-- Row `i ≥ rank ξ` of `0 ⊕ S_ξ` is the stored row. -/
theorem schurRow_of_le {ξ i : ℕ} (hi : T.rank ξ ≤ i) : T.schurRow ξ i = T.schur ξ i := by
  have hlt : Nat.blt i (T.rank ξ) = false := by
    rw [← Bool.not_eq_true, Nat.blt_eq]
    omega
  rw [schurRow, hlt, Bool.cond_false]

/-- The combination of the assembled row, slot by slot: the leaf entry, plus the entries that
the children pass, minus the entry of `0 ⊕ S_ξ`, plus the diagonal term. No bound on the entries
is used. -/
theorem sum_asm (hw : 2 ≤ T.width) {ξ i k : ℕ} (hk : k < T.size ξ) :
    ∑ j ∈ range (Nat.add (T.kids ξ).length 3),
        ((T.asmCoef ξ i j : ℤ) - (Nat.add (T.kidPenalty ξ) 1 : ℕ)) *
          signedSlot T.width k (T.asmRows ξ i j) =
      signedSlot T.width k (T.leaf ξ i) +
        ((T.kids ξ).map fun c ↦ signedSlot T.width (k + T.rank c)
          (T.schur c (i + T.rank c))).sum -
        signedSlot T.width k (T.schurRow ξ i) +
        (if k = i then ((if T.rank ξ ≤ i then (T.lift ξ : ℤ) else 0) - T.kidPenalty ξ)
          else 0) := by
  set n := (T.kids ξ).length with hn
  have e3 : Nat.add n 3 = n + 1 + 1 + 1 := rfl
  rw [e3, sum_range_succ, sum_range_succ, sum_range_succ']
  -- The four kinds of rows, one index at a time.
  have hleaf : T.asmRows ξ i 0 = T.leaf ξ i := rfl
  have hc0 : T.asmCoef ξ i 0 = T.kidPenalty ξ + 2 := rfl
  have hkid : ∀ j ∈ range n, ((T.asmCoef ξ i (j + 1) : ℤ) - (Nat.add (T.kidPenalty ξ) 1 : ℕ)) *
      signedSlot T.width k (T.asmRows ξ i (j + 1)) =
      signedSlot T.width (k + T.rank ((T.kids ξ).getD j 0))
        (T.schur ((T.kids ξ).getD j 0) (i + T.rank ((T.kids ξ).getD j 0))) := by
    intro j hj
    have hj' : j + 1 ≤ n := mem_range.mp hj
    have hble : Nat.ble (j + 1) (T.kids ξ).length = true := Nat.ble_eq.mpr hj'
    have hbeq : Nat.beq (j + 1) 0 = false := rfl
    have hrow : T.asmRows ξ i (j + 1) = T.childRow ((T.kids ξ).getD j 0) i := by
      simp only [asmRows, hbeq, hble, Bool.cond_false, Bool.cond_true]
      rfl
    have hcoef : T.asmCoef ξ i (j + 1) = T.kidPenalty ξ + 2 := by
      simp only [asmCoef, hble, Bool.cond_true]
    have hone : ((T.kidPenalty ξ + 2 : ℕ) : ℤ) - ((Nat.add (T.kidPenalty ξ) 1 : ℕ) : ℤ) = 1 := by
      change ((T.kidPenalty ξ + 2 : ℕ) : ℤ) - ((T.kidPenalty ξ + 1 : ℕ) : ℤ) = 1
      omega
    rw [hrow, hcoef, childRow, signedSlot_shiftRight, hone, one_mul]
    rfl
  have hown : T.asmRows ξ i (n + 1) = T.schurRow ξ i ∧ T.asmCoef ξ i (n + 1) = T.kidPenalty ξ := by
    have hbeq0 : Nat.beq (n + 1) 0 = false := rfl
    have hble : Nat.ble (n + 1) (T.kids ξ).length = false := by
      rw [← Bool.not_eq_true, Nat.ble_eq]
      omega
    have hbeq : Nat.beq (n + 1) (Nat.add (T.kids ξ).length 1) = true := Nat.beq_eq.mpr rfl
    constructor
    · simp only [asmRows, hbeq0, hble, hbeq, Bool.cond_false, Bool.cond_true]
    · simp only [asmCoef, hble, hbeq, Bool.cond_false, Bool.cond_true]
  have hunit : T.asmRows ξ i (n + 1 + 1) = unitRow T.width (T.size ξ) i ∧
      T.asmCoef ξ i (n + 1 + 1) = cond (Nat.ble (T.rank ξ) i) (Nat.add (T.lift ξ) 1) 1 := by
    have hbeq0 : Nat.beq (n + 1 + 1) 0 = false := rfl
    have hble : Nat.ble (n + 1 + 1) (T.kids ξ).length = false := by
      rw [← Bool.not_eq_true, Nat.ble_eq]
      omega
    have hbeq : Nat.beq (n + 1 + 1) (Nat.add (T.kids ξ).length 1) = false := by
      rw [← Bool.not_eq_true, Nat.beq_eq]
      change ¬ n + 1 + 1 = n + 1
      omega
    constructor
    · simp only [asmRows, hbeq0, hble, hbeq, Bool.cond_false]
    · simp only [asmCoef, hble, hbeq, Bool.cond_false]
  rw [sum_congr rfl hkid, sum_range_getD (T.kids ξ) fun c ↦
    signedSlot T.width (k + T.rank c) (T.schur c (i + T.rank c)), hleaf, hc0, hown.1, hown.2,
    hunit.1, hunit.2, signedSlot_unitRow hw hk]
  have hcond : ((cond (Nat.ble (T.rank ξ) i) (Nat.add (T.lift ξ) 1) 1 : ℕ) : ℤ) =
      (if T.rank ξ ≤ i then (T.lift ξ : ℤ) else 0) + 1 := by
    by_cases hi : T.rank ξ ≤ i
    · have : Nat.ble (T.rank ξ) i = true := Nat.ble_eq.mpr hi
      rw [this, Bool.cond_true, ite_eq_left hi]
      change ((T.lift ξ + 1 : ℕ) : ℤ) = _
      push_cast
      ring
    · have : Nat.ble (T.rank ξ) i = false := by
        rw [← Bool.not_eq_true, Nat.ble_eq]
        exact hi
      rw [this, Bool.cond_false, ite_eq_right hi]
      norm_num
  have hoff : ((Nat.add (T.kidPenalty ξ) 1 : ℕ) : ℤ) = (T.kidPenalty ξ : ℤ) + 1 := by
    change ((T.kidPenalty ξ + 1 : ℕ) : ℤ) = _
    push_cast
    rfl
  rw [hcond, hoff]
  push_cast
  split_ifs <;> ring

/-- What node `ξ` needs to know of its children: the chain of a child is its pivots followed by
the chain of `ξ`, and the rows that the child passes satisfy their entry bound. -/
structure KidsReady (ξ : ℕ) : Prop where
  /-- The chain of a child. -/
  size_eq : ∀ c ∈ T.kids ξ, T.size c = T.rank c + T.size ξ
  /-- The entry bound of the passed rows. -/
  guard : ∀ c ∈ T.kids ξ, ∀ i < T.size ξ,
    signedGuardCheck T.width T.schurBits (T.size c) (T.schur c (i + T.rank c)) = true

/-- **The entries of the assembled front.** If the tests of node `ξ` pass and its children are
ready, then for `i, k < size ξ` slot `k` of `asmRow ξ i` is the leaf entry, plus the entries
that the children pass, minus the entry of `0 ⊕ S_ξ`, plus the diagonal term
`[rank ξ ≤ i] lift ξ - kidPenalty ξ`. -/
theorem signedSlot_asmRow {ξ : ℕ} (hnode : T.nodeCheck ξ = true)
    (hrows : ∀ i < T.size ξ, T.rowCheck ξ i = true) (hkids : T.KidsReady ξ) {i k : ℕ}
    (hi : i < T.size ξ) (hk : k < T.size ξ) :
    signedSlot T.width k (T.asmRow ξ i) =
      signedSlot T.width k (T.leaf ξ i) +
        ((T.kids ξ).map fun c ↦ signedSlot T.width (k + T.rank c)
          (T.schur c (i + T.rank c))).sum -
        signedSlot T.width k (T.schurRow ξ i) +
        (if k = i then ((if T.rank ξ ≤ i then (T.lift ξ : ℤ) else 0) - T.kidPenalty ξ)
          else 0) := by
  obtain ⟨hp, hlb, hsb, hfit, -, -, -, -⟩ := T.nodeCheck_spec hnode
  have hw : 2 ≤ T.width := (PackedLDLParams.valid_spec hp).1
  have hrow := T.rowCheck_spec (hrows i hi)
  -- Every combined row is a packed row of `size ξ` slots.
  have hlt : ∀ j < Nat.add (T.kids ξ).length 3, T.asmRows ξ i j < 2 ^ (T.width * T.size ξ) := by
    intro j _
    unfold asmRows
    cases h0 : Nat.beq j 0 with
    | true => exact lt_of_signedGuardCheck hrow.1
    | false =>
      cases hble : Nat.ble j (T.kids ξ).length with
      | true =>
        -- A row of a child, moved down by the pivots of the child.
        have hj0 : j ≠ 0 := by
          rintro rfl
          exact absurd h0 (by decide)
        have hjl : j ≤ (T.kids ξ).length := Nat.ble_eq.mp hble
        have hpos : Nat.sub j 1 < (T.kids ξ).length := by
          change j - 1 < _
          omega
        have hmem : (T.kids ξ).getD (Nat.sub j 1) 0 ∈ T.kids ξ := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpos, Option.getD_some]
          exact List.getElem_mem _
        have hx := lt_of_signedGuardCheck (hkids.guard _ hmem i hi)
        rw [hkids.size_eq _ hmem] at hx
        exact shiftRight_lt hx
      | false =>
        cases Nat.beq j (Nat.add (T.kids ξ).length 1) with
        | false => exact unitRow_lt hw hi
        | true =>
          change T.schurRow ξ i < _
          by_cases hir : T.rank ξ ≤ i
          · rw [T.schurRow_of_le hir]
            exact lt_of_signedGuardCheck (hrow.2.1 hir).1
          · have hlt' : Nat.blt i (T.rank ξ) = true := Nat.blt_eq.mpr (not_le.mp hir)
            rw [schurRow, hlt', Bool.cond_true]
            exact biasRow_lt _ _
  -- Every entry of the combination fits its slot.
  have hfits : ∀ k' < T.size ξ, FitsSlot T.width (∑ j ∈ range (Nat.add (T.kids ξ).length 3),
      ((T.asmCoef ξ i j : ℤ) - (Nat.add (T.kidPenalty ξ) 1 : ℕ)) *
        signedSlot T.width k' (T.asmRows ξ i j)) := by
    intro k' hk'
    rw [T.sum_asm hw hk']
    apply fitsSlot_of_natAbs_le (m := T.asmBound ξ) _ hfit
    have h1 : |(signedSlot T.width k' (T.leaf ξ i) : ℤ)| ≤ slotBias T.leafBits :=
      (Int.abs_eq_natAbs _).trans_le (by
        exact_mod_cast natAbs_signedSlot_le_of_signedGuardCheck hlb hrow.1 hk')
    have h2 : |((T.kids ξ).map fun c ↦ signedSlot T.width (k' + T.rank c)
        (T.schur c (i + T.rank c))).sum| ≤ ((T.kids ξ).length * slotBias T.schurBits : ℕ) := by
      have hall : ∀ c ∈ T.kids ξ, |signedSlot T.width (k' + T.rank c)
          (T.schur c (i + T.rank c))| ≤ (slotBias T.schurBits : ℤ) := by
        intro c hc
        refine (Int.abs_eq_natAbs _).trans_le ?_
        exact_mod_cast natAbs_signedSlot_le_of_signedGuardCheck hsb (hkids.guard c hc i hi)
          (by rw [hkids.size_eq c hc]; omega)
      generalize T.kids ξ = l at hall ⊢
      induction l with
      | nil => simp
      | cons c l ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        refine (abs_add_le _ _).trans ?_
        have hc := hall c (by simp)
        have hl := ih fun c' hc' ↦ hall c' (by simp [hc'])
        push_cast at hl ⊢
        linarith
    have h3 : |(signedSlot T.width k' (T.schurRow ξ i) : ℤ)| ≤ slotBias T.schurBits := by
      by_cases hir : T.rank ξ ≤ i
      · rw [T.schurRow_of_le hir]
        refine (Int.abs_eq_natAbs _).trans_le ?_
        exact_mod_cast natAbs_signedSlot_le_of_signedGuardCheck hsb (hrow.2.1 hir).1 hk'
      · rw [T.signedSlot_schurRow_of_lt hk' (not_le.mp hir)]
        simp
    have h4 : |(if k' = i then ((if T.rank ξ ≤ i then (T.lift ξ : ℤ) else 0) - T.kidPenalty ξ)
        else 0)| ≤ ((T.lift ξ + T.kidPenalty ξ : ℕ) : ℤ) := by
      push_cast
      split_ifs <;> rw [abs_le] <;> constructor <;> linarith [Int.natCast_nonneg (T.lift ξ),
        Int.natCast_nonneg (T.kidPenalty ξ)]
    have htot := (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add h1 h2)) h3)) h4)
    rw [Int.abs_eq_natAbs] at htot
    have hb : T.asmBound ξ = slotBias T.leafBits +
        ((T.kids ξ).length + 1) * slotBias T.schurBits + T.lift ξ + T.kidPenalty ξ := rfl
    rw [hb]
    have : ((signedSlot T.width k' (T.leaf ξ i) +
        ((T.kids ξ).map fun c ↦ signedSlot T.width (k' + T.rank c)
          (T.schur c (i + T.rank c))).sum - signedSlot T.width k' (T.schurRow ξ i) +
        (if k' = i then ((if T.rank ξ ≤ i then (T.lift ξ : ℤ) else 0) - T.kidPenalty ξ)
          else 0)).natAbs : ℤ) ≤ ((slotBias T.leafBits +
        ((T.kids ξ).length + 1) * slotBias T.schurBits + T.lift ξ + T.kidPenalty ξ : ℕ) : ℤ) := by
      push_cast at htot ⊢
      linarith
    exact_mod_cast this
  unfold asmRow
  rw [signedSlot_packedRowCombination hlt hfits hk, T.sum_asm hw hk]

/-- **The inequality of one node.** If `scale` is positive, the tests of node `ξ` pass and its
children are ready, then for every chain vector `y`
`gain ξ * |y_pivots|² + pass ξ (y after the pivots) ≤ leafForm ξ y + ∑ children, pass c y`.

The packed `LDLᵀ` check of the assembled front bounds the form of
`leaf + ∑ (S_c - P_c) - (0 ⊕ S_ξ) + lift (0 ⊕ I)` from below by `(lift - size ε / a) |y|²`;
the term with `lift` cancels on the slots after the pivots, where the penalty of `ξ` covers the
residual. -/
theorem node_ge {ξ : ℕ} (hscale : 0 < T.scale) (hnode : T.nodeCheck ξ = true)
    (hrows : ∀ i < T.size ξ, T.rowCheck ξ i = true) (hkids : T.KidsReady ξ) (y : ℕ → ℝ) :
    T.gain ξ * rangeSq (T.rank ξ) y + T.pass ξ (fun p ↦ y (p + T.rank ξ)) ≤
      T.leafForm ξ y + ((T.kids ξ).map fun c ↦ T.pass c y).sum := by
  obtain ⟨hp, -, -, -, hpen, -, -, -⟩ := T.nodeCheck_spec hnode
  have hrank : T.rank ξ ≤ T.size ξ := (PackedLDLParams.valid_spec hp).2.2.2.2.1
  set c := T.size ξ with hc
  set r := T.rank ξ with hr
  obtain ⟨m, hm⟩ : ∃ m, c = r + m := ⟨c - r, by omega⟩
  have hsub : c - r = m := by omega
  -- The packed check of the assembled front.
  have hmain : (((T.scale * T.lift ξ : ℕ) : ℝ) - (c : ℝ) * slotBias T.residualBits) *
      ∑ i : Fin c, y i.val ^ 2 ≤ (T.scale : ℝ) * ∑ i : Fin c, ∑ j : Fin c,
        (signedSlot T.width j.val (T.asmRow ξ i.val) : ℝ) * y i.val * y j.val :=
    quadForm_ge_of_ldltRowCheck (T.params ξ) (T.asmRow ξ) (T.factor ξ) (T.weight ξ)
      hp (fun i hi ↦ (T.rowCheck_spec (hrows i hi)).2.2) (fun i ↦ y i.val)
  have hsq : ∑ i : Fin c, y i.val ^ 2 = rangeSq c y := Fin.sum_univ_eq_sum_range (fun i ↦ y i ^ 2) c
  have hform : ∑ i : Fin c, ∑ j : Fin c,
      (signedSlot T.width j.val (T.asmRow ξ i.val) : ℝ) * y i.val * y j.val =
      rangeForm c (fun i j ↦ (signedSlot T.width j (T.asmRow ξ i) : ℝ)) y := by
    rw [rangeForm, ← Fin.sum_univ_eq_sum_range (fun i ↦ ∑ j ∈ range c,
      (signedSlot T.width j (T.asmRow ξ i) : ℝ) * y i * y j) c]
    exact sum_congr rfl fun i _ ↦ Fin.sum_univ_eq_sum_range (fun j ↦
      (signedSlot T.width j (T.asmRow ξ i.val) : ℝ) * y i.val * y j) c
  rw [hsq, hform, Nat.cast_mul] at hmain
  -- The assembled front, entry by entry.
  have hentries : rangeForm c (fun i j ↦ (signedSlot T.width j (T.asmRow ξ i) : ℝ)) y =
      rangeForm c (fun i j ↦ (signedSlot T.width j (T.leaf ξ i) : ℝ) +
        ((T.kids ξ).map fun ch ↦ T.passEntry ch i j).sum -
        (signedSlot T.width j (T.schurRow ξ i) : ℝ) +
        (if j = i then ((if r ≤ i then (T.lift ξ : ℝ) else 0) - T.kidPenalty ξ) else 0)) y := by
    refine rangeForm_congr (fun i hi j hj ↦ ?_) y
    rw [T.signedSlot_asmRow hnode hrows hkids hi hj, Int.cast_add, Int.cast_sub, Int.cast_add,
      cast_list_sum_map, ← hr]
    simp only [passEntry]
    congr 1
    split_ifs <;> simp
  -- The four parts of the form.
  have hkidsForm : rangeForm c (fun i j ↦ ((T.kids ξ).map fun ch ↦ T.passEntry ch i j).sum) y =
      ((T.kids ξ).map fun ch ↦ T.pass ch y).sum + T.kidPenalty ξ * rangeSq c y := by
    rw [rangeForm_list_sum]
    have hall : ∀ ch ∈ T.kids ξ, rangeForm c (T.passEntry ch) y =
        T.pass ch y + T.penalty ch * rangeSq c y := by
      intro ch hch
      have : T.size ch - T.rank ch = c := by rw [hkids.size_eq ch hch]; omega
      rw [pass, this]
      ring
    have hpenalty : (T.kidPenalty ξ : ℝ) = ((T.kids ξ).map fun ch ↦ (T.penalty ch : ℝ)).sum := by
      rw [kidPenalty]
      generalize T.kids ξ = l
      induction l with
      | nil => simp
      | cons ch l ih => simp [ih]
    rw [hpenalty]
    generalize T.kids ξ = l at hall ⊢
    induction l with
    | nil => simp
    | cons ch l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [hall ch (by simp), ih fun ch' hch' ↦ hall ch' (by simp [hch'])]
      ring
  have hownForm : rangeForm c (fun i j ↦ (signedSlot T.width j (T.schurRow ξ i) : ℝ)) y =
      T.pass ξ (fun p ↦ y (p + r)) + T.penalty ξ * rangeSq m (fun p ↦ y (p + r)) := by
    have hzero : rangeForm c (fun i j ↦ (signedSlot T.width j (T.schurRow ξ i) : ℝ)) y =
        rangeForm c (fun i j ↦ if r ≤ i ∧ r ≤ j then
          (signedSlot T.width j (T.schurRow ξ i) : ℝ) else 0) y := by
      refine rangeForm_congr (fun i hi j hj ↦ ?_) y
      by_cases hir : r ≤ i
      · by_cases hjr : r ≤ j
        · rw [ite_eq_left ⟨hir, hjr⟩]
        · rw [ite_eq_right (fun h ↦ hjr h.2), T.schurRow_of_le hir,
            signedSlot_eq_zero_of_land ((T.rowCheck_spec (hrows i hi)).2.1 hir).2
              (not_le.mp hjr)]
          simp
      · rw [ite_eq_right (fun h ↦ hir h.1), T.signedSlot_schurRow_of_lt hj (not_le.mp hir)]
        simp
    rw [hzero, hm, rangeForm_shift (fun i hi j ↦ ite_eq_right fun h ↦ by omega)
      (fun i j hj ↦ ite_eq_right fun h ↦ by omega), pass, hsub]
    have : rangeForm m (fun i j ↦ if r ≤ i + r ∧ r ≤ j + r then
        (signedSlot T.width (j + r) (T.schurRow ξ (i + r)) : ℝ) else 0) (fun p ↦ y (p + r)) =
        rangeForm m (T.passEntry ξ) (fun p ↦ y (p + r)) := by
      refine rangeForm_congr (fun i _ j _ ↦ ?_) _
      rw [ite_eq_left ⟨by omega, by omega⟩, T.schurRow_of_le (by omega), passEntry]
    rw [this]
    ring
  have hdiag : rangeForm c (fun i j ↦ if j = i then
      ((if r ≤ i then (T.lift ξ : ℝ) else 0) - T.kidPenalty ξ) else 0) y =
      T.lift ξ * rangeSq m (fun p ↦ y (p + r)) - T.kidPenalty ξ * rangeSq c y := by
    rw [rangeForm_diag, rangeSq, rangeSq, mul_sum, mul_sum, hm, sum_range_add, sum_range_add]
    have h1 : ∀ i ∈ range r, ((if r ≤ i then (T.lift ξ : ℝ) else 0) - T.kidPenalty ξ) * y i ^ 2 =
        -(T.kidPenalty ξ * y i ^ 2) := by
      intro i hi
      rw [ite_eq_right (by have := mem_range.mp hi; omega)]
      ring
    have h2 : ∀ i ∈ range m, ((if r ≤ r + i then (T.lift ξ : ℝ) else 0) - T.kidPenalty ξ) *
        y (r + i) ^ 2 = T.lift ξ * y (i + r) ^ 2 - T.kidPenalty ξ * y (r + i) ^ 2 := by
      intro i _
      rw [ite_eq_left (by omega), Nat.add_comm i r]
      ring
    rw [sum_congr rfl h1, sum_congr rfl h2, sum_neg_distrib, sum_sub_distrib]
    ring
  have hsplit : rangeSq c y = rangeSq r y + rangeSq m (fun p ↦ y (p + r)) := by
    rw [hm, rangeSq_add]
  rw [hentries, rangeForm_add, rangeForm_sub, rangeForm_add, hkidsForm, hownForm, hdiag] at hmain
  -- The scalar inequality.
  have ha : (0 : ℝ) < T.scale := by exact_mod_cast hscale
  have hpen' : (c : ℝ) * slotBias T.residualBits ≤ T.scale * T.penalty ξ := by
    exact_mod_cast hpen
  have hR : 0 ≤ rangeSq m (fun p ↦ y (p + r)) := sum_nonneg fun i _ ↦ sq_nonneg _
  have hleaf : rangeForm c (fun i j ↦ (signedSlot T.width j (T.leaf ξ i) : ℝ)) y =
      T.leafForm ξ y := rfl
  rw [hleaf, hsplit] at hmain
  rw [gain, div_mul_eq_mul_div, div_add' _ _ _ ha.ne', div_le_iff₀ ha]
  nlinarith [mul_nonneg (sub_nonneg.mpr hpen') hR]

/-- **Telescoping along the tree.** If `scale` is positive and `nodeCheck` and every `rowCheck`
pass at every node, then for every family of chain vectors `y ξ` that agree along the tree
(`y ξ (p + rank ξ) = y (parent ξ) p` for the slots `p` of the parent),
`∑ ξ, gain ξ * |pivots of y ξ|² ≤ ∑ ξ, leafForm ξ (y ξ)`.

The inequalities of the nodes are added. The form that a node passes occurs once on the left,
at the node, and once on the right, at its parent; the root passes a form on no slots. -/
theorem sum_gain_le (hscale : 0 < T.scale) (hnodes : ∀ ξ < T.nodes, T.nodeCheck ξ = true)
    (hrows : ∀ ξ < T.nodes, ∀ i < T.size ξ, T.rowCheck ξ i = true) (y : ℕ → ℕ → ℝ)
    (hy : ∀ ξ, ξ + 1 < T.nodes → ∀ p < T.size (T.parent ξ),
      y ξ (p + T.rank ξ) = y (T.parent ξ) p) :
    ∑ ξ ∈ range T.nodes, T.gain ξ * rangeSq (T.rank ξ) (y ξ) ≤
      ∑ ξ ∈ range T.nodes, T.leafForm ξ (y ξ) := by
  -- The children of a node are ready.
  have hready : ∀ ξ < T.nodes, T.KidsReady ξ := by
    intro ξ hξ
    have hmem : ∀ c ∈ T.kids ξ, c + 1 < T.nodes ∧ T.parent c = ξ := fun c hc ↦ by
      have := (T.mem_kids_iff (hnodes ξ hξ)).mp hc
      exact ⟨by omega, this.2⟩
    refine ⟨fun c hc ↦ ?_, fun c hc i hi ↦ ?_⟩
    · have h := ((T.nodeCheck_spec (hnodes c (by have := hmem c hc; omega))).2.2.2.2.2.2.1
        (hmem c hc).1).2.2
      rwa [(hmem c hc).2] at h
    · have hcn : c < T.nodes := by have := hmem c hc; omega
      have hsize := ((T.nodeCheck_spec (hnodes c hcn)).2.2.2.2.2.2.1 (hmem c hc).1).2.2
      rw [(hmem c hc).2] at hsize
      exact ((T.rowCheck_spec (hrows c hcn (i + T.rank c) (by omega))).2.1 (by omega)).1
  -- The form that a node passes, as its parent sees it.
  set up : ℕ → ℝ := fun ξ ↦ T.pass ξ (fun p ↦ y ξ (p + T.rank ξ)) with hup
  have hnode : ∀ ξ ∈ range T.nodes, T.gain ξ * rangeSq (T.rank ξ) (y ξ) + up ξ ≤
      T.leafForm ξ (y ξ) + ((T.kids ξ).map fun c ↦ up c).sum := by
    intro ξ hξ
    have hξ' := mem_range.mp hξ
    have h := T.node_ge hscale (hnodes ξ hξ') (hrows ξ hξ') (hready ξ hξ') (y ξ)
    have hkid : ((T.kids ξ).map fun c ↦ T.pass c (y ξ)) = (T.kids ξ).map fun c ↦ up c := by
      refine List.map_congr_left fun c hc ↦ ?_
      have hmem := (T.mem_kids_iff (hnodes ξ hξ')).mp hc
      have hc1 : c + 1 < T.nodes := by omega
      have hsize := ((T.nodeCheck_spec (hnodes c (by omega))).2.2.2.2.2.2.1 hc1).2.2
      have hsub : T.size c - T.rank c = T.size (T.parent c) := by omega
      have hagree : ∀ p < T.size c - T.rank c, y ξ p = y c (p + T.rank c) := fun p hp ↦ by
        rw [hy c hc1 p (by omega), hmem.2]
      simp only [hup, pass]
      rw [rangeForm_congr_vec _ hagree, rangeSq_congr hagree]
    rwa [hkid] at h
  have hsum := sum_le_sum hnode
  rw [sum_add_distrib, sum_add_distrib] at hsum
  -- Every node other than the root is a child of exactly one node.
  have hkidsum : ∑ ξ ∈ range T.nodes, ((T.kids ξ).map fun c ↦ up c).sum =
      ∑ c ∈ range T.nodes, if c + 1 < T.nodes then up c else 0 := by
    have h1 : ∀ ξ ∈ range T.nodes, ((T.kids ξ).map fun c ↦ up c).sum =
        ∑ c ∈ range T.nodes, if c < ξ ∧ T.parent c = ξ then up c else 0 := by
      intro ξ hξ
      have hξ' := mem_range.mp hξ
      rw [(T.nodeCheck_spec (hnodes ξ hξ')).2.2.2.2.2.1, ← List.sum_toFinset _
        (List.Nodup.filter _ List.nodup_range), ← sum_filter]
      refine sum_congr ?_ fun _ _ ↦ rfl
      ext c
      simp only [List.mem_toFinset, List.mem_filter, List.mem_range, Nat.beq_eq, mem_filter,
        mem_range]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h1, h2⟩
      · rintro ⟨-, h1, h2⟩
        exact ⟨h1, h2⟩
    rw [sum_congr rfl h1, sum_comm]
    refine sum_congr rfl fun c hc ↦ ?_
    have hc' := mem_range.mp hc
    by_cases hc1 : c + 1 < T.nodes
    · obtain ⟨hlt, hpn, -⟩ := (T.nodeCheck_spec (hnodes c hc')).2.2.2.2.2.2.1 hc1
      rw [ite_eq_left hc1, sum_eq_single (T.parent c)]
      · rw [ite_eq_left ⟨hlt, rfl⟩]
      · intro ξ _ hne
        rw [ite_eq_right fun h ↦ hne h.2.symm]
      · intro h
        exact absurd (mem_range.mpr hpn) h
    · rw [ite_eq_right hc1]
      exact sum_eq_zero fun ξ hξ ↦ ite_eq_right fun h ↦ by
        have := mem_range.mp hξ
        omega
  -- The root passes a form on no slots.
  have hupsum : ∑ ξ ∈ range T.nodes, up ξ =
      ∑ c ∈ range T.nodes, if c + 1 < T.nodes then up c else 0 := by
    refine sum_congr rfl fun c hc ↦ ?_
    by_cases hc1 : c + 1 < T.nodes
    · rw [ite_eq_left hc1]
    · rw [ite_eq_right hc1]
      have hsize := (T.nodeCheck_spec (hnodes c (mem_range.mp hc))).2.2.2.2.2.2.2 hc1
      simp only [hup, pass, hsize, Nat.sub_self, rangeForm, rangeSq, range_zero, sum_empty,
        mul_zero, sub_zero]
  rw [hkidsum, hupsum] at hsum
  linarith

/-- **The assembled form of all the unknowns.** Let `chain ξ p` be the unknown in slot `p` of the
chain of node `ξ`, with `chain ξ (p + rank ξ) = chain (parent ξ) p`. If `scale` is positive and
the tests of every node pass, then for every real vector `x` of the unknowns the assembled form
`∑ ξ, leafForm ξ (x ∘ chain ξ)` is at least `∑ ξ, gain ξ * ∑ p < rank ξ, x (chain ξ p) ^ 2`.
With positive gains and every unknown a pivot of one node, the assembled quadratic form is
positive at every nonzero vector. The statement is about the form: no matrix is formed, and the
symmetry that Mathlib's `Matrix.PosDef` asks for is not part of it. -/
theorem sum_gain_le_global (hscale : 0 < T.scale) (hnodes : ∀ ξ < T.nodes, T.nodeCheck ξ = true)
    (hrows : ∀ ξ < T.nodes, ∀ i < T.size ξ, T.rowCheck ξ i = true) (chain : ℕ → ℕ → ℕ)
    (hchain : ∀ ξ, ξ + 1 < T.nodes → ∀ p < T.size (T.parent ξ),
      chain ξ (p + T.rank ξ) = chain (T.parent ξ) p) (x : ℕ → ℝ) :
    ∑ ξ ∈ range T.nodes, T.gain ξ * ∑ p ∈ range (T.rank ξ), x (chain ξ p) ^ 2 ≤
      ∑ ξ ∈ range T.nodes, T.leafForm ξ (fun p ↦ x (chain ξ p)) :=
  T.sum_gain_le hscale hnodes hrows (fun ξ p ↦ x (chain ξ p)) fun ξ hξ p hp ↦ by
    rw [hchain ξ hξ p hp]

/-- For a positive `scale`, if `scale * g + size ξ * ε ≤ scale * lift ξ`, the margin of node `ξ`
is at least `g`: a comparison of natural numbers that the kernel decides. -/
theorem le_gain {ξ g : ℕ} (hscale : 0 < T.scale)
    (h : T.scale * g + T.size ξ * slotBias T.residualBits ≤ T.scale * T.lift ξ) :
    (g : ℝ) ≤ T.gain ξ := by
  have ha : (0 : ℝ) < T.scale := by exact_mod_cast hscale
  have h' : (T.scale : ℝ) * g + T.size ξ * slotBias T.residualBits ≤ T.scale * T.lift ξ := by
    exact_mod_cast h
  rw [gain, le_div_iff₀ ha]
  linarith

/-- **A uniform margin.** If `scale` is positive, the tests of every node pass and the margin of
every node is at least the natural number `g`, then
`g * ∑ ξ, ∑ p < rank ξ, x (chain ξ p) ^ 2` is at most the assembled form
`∑ ξ, leafForm ξ (x ∘ chain ξ)`, for every real vector `x`. It is `sum_gain_le_global` with each
margin replaced by `g`. -/
theorem uniform_le_global (hscale : 0 < T.scale) (hnodes : ∀ ξ < T.nodes, T.nodeCheck ξ = true)
    (hrows : ∀ ξ < T.nodes, ∀ i < T.size ξ, T.rowCheck ξ i = true) (chain : ℕ → ℕ → ℕ)
    (hchain : ∀ ξ, ξ + 1 < T.nodes → ∀ p < T.size (T.parent ξ),
      chain ξ (p + T.rank ξ) = chain (T.parent ξ) p) {g : ℕ}
    (hg : ∀ ξ < T.nodes, T.scale * g + T.size ξ * slotBias T.residualBits ≤ T.scale * T.lift ξ)
    (x : ℕ → ℝ) :
    (g : ℝ) * ∑ ξ ∈ range T.nodes, ∑ p ∈ range (T.rank ξ), x (chain ξ p) ^ 2 ≤
      ∑ ξ ∈ range T.nodes, T.leafForm ξ (fun p ↦ x (chain ξ p)) := by
  rw [mul_sum]
  exact (sum_le_sum fun ξ hξ ↦ mul_le_mul_of_nonneg_right
    (T.le_gain hscale (hg ξ (mem_range.mp hξ))) (sum_nonneg fun p _ ↦ sq_nonneg _)).trans
    (T.sum_gain_le_global hscale hnodes hrows chain hchain x)

/-! ### Columns: a positive term of low rank on the leaves -/

/-- Columns of a tree of fronts: node `ξ` has `count ξ` packed rows `col ξ c` on its chain, with
entries of at most `slotBias bits` in absolute value. The leaf rows of the tree itself have
entries of at most `slotBias leafBits`. -/
structure Cols where
  /-- The number of columns of a node. -/
  count : ℕ → ℕ
  /-- Column `c` of a node, a packed row on the chain of the node. -/
  col : ℕ → ℕ → ℕ
  /-- Column entries are at most `slotBias bits` in absolute value. -/
  bits : ℕ
  /-- Leaf entries of the tree are at most `slotBias leafBits` in absolute value. -/
  leafBits : ℕ

/-- Row `i` of the leaf matrix of node `ξ` plus the outer products `y yᵀ` of its columns: the
row of `LowRankLDL` for the negated leaf row with coefficient `-1` and weights `1`. For a node
without columns it is the leaf row itself, which the kernel then reads without any arithmetic. -/
def colsRow (C : Cols) (ξ i : ℕ) : ℕ :=
  cond (Nat.beq (C.count ξ) 0) (T.leaf ξ i)
    (lowRankRow T.width (T.size ξ) (C.count ξ) (slotBias C.bits) 1
      (fun l ↦ negRow T.width (T.size ξ) (T.leaf ξ l)) (C.col ξ) (fun _ ↦ 1) (fun _ ↦ 0) i)

/-- The tree whose leaf matrices are those of `T` plus the outer products of the columns. -/
def withCols (C : Cols) : FrontTree := { T with leaf := T.colsRow C }

/-- The test of the columns of node `ξ`: the bit bounds are below the width, the entry bound of
every column, and the fit of the leaf rows with the outer products. -/
def colsCheck (C : Cols) (ξ : ℕ) : Bool :=
  Nat.ble 2 T.width && Nat.blt C.bits T.width && Nat.blt C.leafBits T.width &&
    Nat.ble 1 (slotBias C.bits) &&
    natAll (C.count ξ) (fun c ↦ signedGuardCheck T.width C.bits (T.size ξ) (C.col ξ c)) &&
    Nat.blt (Nat.mul 2 (Nat.add (Nat.mul (C.count ξ)
      (Nat.mul (slotBias C.bits) (slotBias C.bits))) (slotBias C.leafBits)))
      (Nat.shiftLeft 1 T.width)

/-- The test of row `i` of node `ξ` for the columns: the entry bound of the leaf row of `T`. -/
def colsRowCheck (C : Cols) (ξ i : ℕ) : Bool :=
  signedGuardCheck T.width C.leafBits (T.size ξ) (T.leaf ξ i)

/-- The form of the columns of node `ξ` on a chain vector: the sum of the squares of the columns
applied to the vector. -/
def colForm (C : Cols) (ξ : ℕ) (y : ℕ → ℝ) : ℝ :=
  ∑ c ∈ range (C.count ξ),
    (∑ i ∈ range (T.size ξ), (signedSlot T.width i (C.col ξ c) : ℝ) * y i) ^ 2

/-- **The entries of a leaf row with columns.** If the tests of the columns pass, slot `k` of
`colsRow` is the leaf entry plus `∑ c, y_c i * y_c k`. -/
theorem signedSlot_colsRow (C : Cols) {ξ i k : ℕ} (hc : T.colsCheck C ξ = true)
    (hrow : T.colsRowCheck C ξ i = true) (hi : i < T.size ξ) (hk : k < T.size ξ) :
    signedSlot T.width k (T.colsRow C ξ i) = signedSlot T.width k (T.leaf ξ i) +
      ∑ c ∈ range (C.count ξ),
        signedSlot T.width i (C.col ξ c) * signedSlot T.width k (C.col ξ c) := by
  by_cases h0 : C.count ξ = 0
  · unfold colsRow
    rw [h0, Nat.beq_refl, Bool.cond_true, range_zero, sum_empty, add_zero]
  have hb : Nat.beq (C.count ξ) 0 = false :=
    Bool.eq_false_iff.mpr fun h ↦ h0 (Nat.eq_of_beq_eq_true h)
  simp only [colsCheck, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hc
  obtain ⟨⟨⟨⟨⟨hw, hcb⟩, hlb⟩, hα⟩, hguard⟩, hfit⟩ := hc
  have hw0 : 0 < T.width := by omega
  have hleaf : signedGuardCheck T.width C.leafBits (T.size ξ) (T.leaf ξ i) = true := hrow
  have hx := lt_of_signedGuardCheck hleaf
  have hpos : ∀ j < T.size ξ, 0 < slot T.width j (T.leaf ξ i) := fun j hj ↦
    slot_pos_of_signedGuardCheck hlb hleaf hj
  have hfit' : 2 * (C.count ξ * (slotBias C.bits * 1 * slotBias C.bits) +
      1 * slotBias C.leafBits + 0) < 2 ^ T.width := by
    change 2 * (C.count ξ * (slotBias C.bits * slotBias C.bits) + slotBias C.leafBits) <
      1 <<< T.width at hfit
    rw [Nat.one_shiftLeft] at hfit
    simpa using hfit
  have h := signedSlot_lowRankRow (w := T.width) (n := T.size ξ) (m := C.count ξ)
    (α := slotBias C.bits) (c := 1)
    (Arow := fun l ↦ negRow T.width (T.size ξ) (T.leaf ξ l)) (Vcol := C.col ξ)
    (t := fun _ ↦ 1) (g := fun _ ↦ 0) (BA := slotBias C.leafBits) (BV := slotBias C.bits)
    (T := 1) (G := 0) (i := i) (k := k) hw hi hk (negRow_lt hw0 hx hpos)
    (fun l hl ↦ by
      rw [signedSlot_negRow hw0 hx hpos hl, Int.natAbs_neg]
      exact natAbs_signedSlot_le_of_signedGuardCheck hlb hleaf hl)
    (fun j hj ↦ lt_of_signedGuardCheck (natAll_spec hguard hj))
    (fun j hj l hl ↦ natAbs_signedSlot_le_of_signedGuardCheck hcb (natAll_spec hguard hj) hl)
    (fun _ _ ↦ le_rfl) le_rfl hα (by rw [Nat.mul_one]) hfit'
  unfold colsRow
  rw [hb, Bool.cond_false, h, signedSlot_negRow hw0 hx hpos hk]
  simp only [Nat.cast_one, mul_one, one_mul, sub_neg_eq_add, Nat.cast_zero, ite_self,
    add_zero]
  ring

/-- **The leaf form with columns.** If the tests of the columns of node `ξ` pass, the leaf form
of `T.withCols C` is the leaf form of `T` plus the form of the columns. -/
theorem leafForm_withCols (C : Cols) {ξ : ℕ} (hc : T.colsCheck C ξ = true)
    (hrows : ∀ i < T.size ξ, T.colsRowCheck C ξ i = true) (y : ℕ → ℝ) :
    (T.withCols C).leafForm ξ y = T.leafForm ξ y + T.colForm C ξ y := by
  change rangeForm (T.size ξ) (fun i j ↦ (signedSlot T.width j (T.colsRow C ξ i) : ℝ)) y = _
  have hentries : rangeForm (T.size ξ)
      (fun i j ↦ (signedSlot T.width j (T.colsRow C ξ i) : ℝ)) y =
      rangeForm (T.size ξ) (fun i j ↦ (signedSlot T.width j (T.leaf ξ i) : ℝ) +
        ∑ c ∈ range (C.count ξ), (signedSlot T.width i (C.col ξ c) : ℝ) *
          (signedSlot T.width j (C.col ξ c) : ℝ)) y := by
    refine rangeForm_congr (fun i hi j hj ↦ ?_) y
    rw [T.signedSlot_colsRow C hc (hrows i hi) hi hj]
    push_cast
    rfl
  rw [hentries, rangeForm_add, rangeForm_sum_outer]
  rfl

/-- **The assembled form with columns.** Let `scale` be positive, let the tests of every node and
row pass for the tree `T.withCols C`, together with the tests of the columns, and let every
margin be at least the natural number `g`. Then for every real vector `x`,
`g * ∑ ξ, ∑ p < rank ξ, x (chain ξ p) ^ 2`
is at most `∑ ξ, leafForm ξ (x ∘ chain ξ) + ∑ ξ, colForm ξ (x ∘ chain ξ)`:
the assembled matrix of `T` may have negative directions, as many as the columns make up for.
It is `uniform_le_global` for the tree with the outer products of the columns added to its
leaves. -/
theorem uniform_le_global_cols (C : Cols) (hscale : 0 < T.scale)
    (hnodes : ∀ ξ < T.nodes, (T.withCols C).nodeCheck ξ = true)
    (hrows : ∀ ξ < T.nodes, ∀ i < T.size ξ, (T.withCols C).rowCheck ξ i = true)
    (hcols : ∀ ξ < T.nodes, T.colsCheck C ξ = true)
    (hleaf : ∀ ξ < T.nodes, ∀ i < T.size ξ, T.colsRowCheck C ξ i = true) (chain : ℕ → ℕ → ℕ)
    (hchain : ∀ ξ, ξ + 1 < T.nodes → ∀ p < T.size (T.parent ξ),
      chain ξ (p + T.rank ξ) = chain (T.parent ξ) p) {g : ℕ}
    (hg : ∀ ξ < T.nodes, T.scale * g + T.size ξ * slotBias T.residualBits ≤ T.scale * T.lift ξ)
    (x : ℕ → ℝ) :
    (g : ℝ) * ∑ ξ ∈ range T.nodes, ∑ p ∈ range (T.rank ξ), x (chain ξ p) ^ 2 ≤
      ∑ ξ ∈ range T.nodes, T.leafForm ξ (fun p ↦ x (chain ξ p)) +
        ∑ ξ ∈ range T.nodes, T.colForm C ξ (fun p ↦ x (chain ξ p)) := by
  have h := (T.withCols C).uniform_le_global hscale hnodes hrows chain hchain hg x
  rw [← sum_add_distrib]
  refine h.trans_eq (sum_congr rfl fun ξ hξ ↦ ?_)
  have hξ' := mem_range.mp hξ
  exact T.leafForm_withCols C (hcols ξ hξ') (hleaf ξ hξ') _

/-! ### Rows that a front does not touch -/

/-- The test of the mask `idle ξ` of node `ξ`: every factor column of the node has a zero entry
at every slot of the mask. One conjunction per factor column. -/
def idleCheck (idle : ℕ → ℕ) (ξ : ℕ) : Bool :=
  natAll (T.rank ξ) fun j ↦
    Nat.beq (Nat.land (T.factor ξ j) (idle ξ)) (Nat.land (biasRow T.width (T.size ξ)) (idle ξ))

/-- Row `i` of node `ξ` is marked idle: it is not a pivot row, and its slot of the mask is all
ones. -/
def isIdle (idle : ℕ → ℕ) (ξ i : ℕ) : Bool :=
  Nat.ble (T.rank ξ) i && Nat.beq (slot T.width i (idle ξ)) (slotMask T.width)

/-- The test of row `i` of node `ξ` with the cheap residual row for the rows marked idle; the
other rows have the test `rowCheck`. -/
def fastRowCheck (idle : ℕ → ℕ) (ξ i : ℕ) : Bool :=
  cond (T.isIdle idle ξ i)
    (signedGuardCheck T.width T.leafBits (T.size ξ) (T.leaf ξ i) &&
      (signedGuardCheck T.width T.schurBits (T.size ξ) (T.schur ξ i) &&
        Nat.beq (Nat.land (T.schur ξ i) (slotMask (Nat.mul T.width (T.rank ξ))))
          (biasRow T.width (T.rank ξ))) &&
      (signedGuardCheck (T.params ξ).width (T.params ξ).matrixBits (T.params ξ).size
          (T.asmRow ξ i) &&
        signedGuardCheck (T.params ξ).width (T.params ξ).residualBits (T.params ξ).size
          (idleResidualRow (T.params ξ) (T.asmRow ξ) i)))
    (T.rowCheck ξ i)

/-- **The cheap test of an idle row gives the test of the row.** If the mask of node `ξ` passes
`idleCheck` and row `i` passes `fastRowCheck`, then row `i` passes `rowCheck`. So the theorems
of this module hold with `fastRowCheck` and `idleCheck` in place of `rowCheck`, and a row that
the front of a node does not touch costs a few row operations instead of one per pivot. -/
theorem rowCheck_of_fast (idle : ℕ → ℕ) {ξ i : ℕ} (hnode : T.idleCheck idle ξ = true)
    (hi : i < T.size ξ) (h : T.fastRowCheck idle ξ i = true) : T.rowCheck ξ i = true := by
  unfold fastRowCheck at h
  cases hidle : T.isIdle idle ξ i with
  | false =>
    rw [hidle] at h
    exact h
  | true =>
    rw [hidle] at h
    simp only [Bool.cond_true, Bool.and_eq_true] at h
    obtain ⟨⟨hleaf, hschur, hland⟩, hM, hres⟩ := h
    simp only [isIdle, Bool.and_eq_true, Nat.ble_eq] at hidle
    obtain ⟨hrank, hmask⟩ := hidle
    have hmask := Nat.eq_of_beq_eq_true hmask
    have hzero : ∀ j < (T.params ξ).columns i,
        slot (T.params ξ).width i (T.factor ξ j) = slotBias (T.params ξ).width := by
      intro j hj
      have hjr : j < T.rank ξ := lt_of_lt_of_le hj ((T.params ξ).columns_le_rank i)
      have hl := Nat.eq_of_beq_eq_true (natAll_spec hnode hjr)
      change slot T.width i (T.factor ξ j) = slotBias T.width
      rw [slot_eq_of_land_eq hmask hl, biasRow_eq_packSlots,
        slot_packed_eq (fun _ _ ↦ slotBias_lt _), ite_eq_left hi]
    have hnot : Nat.blt i (T.rank ξ) = false := by
      simp only [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
      omega
    have hnot' : Nat.blt i (T.params ξ).rank = false := hnot
    rw [rowCheck, ldltRowCheck, ldltResidualRow_eq_idle hzero, hnot, hnot', hleaf, hschur, hland,
      hM, hres]
    rfl

end FrontTree

end CAS.Numerics

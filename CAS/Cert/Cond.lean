/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Cert.Ball
public import CAS.Cert.Check
public import Mathlib.Data.Stream.Defs

/-!
# Conditions: a small language for the statements of a numerical certificate

## Motivation

The hypotheses of a computer-assisted theorem are inequalities between real expressions of
stored data, for every index of a table, for every point of every cell of a mesh, for every pair
of cells. Is there one language in which all of them are written, with one program that tests a
condition and one theorem that says what a passing test proves?

## The idea

A condition `Cond ι` is a tree. Its leaves compare two real expressions (`le`, `lt`, `eq`) in
the variables `ι ⊕ ℕ`: `Sum.inl i` is the entry `i` of the data, `Sum.inr v` the cell variable
`v`. Its inner nodes are:

* `and` and `or`;
* `all n body`: for every `k < n`, the condition `body k`. Here `body` is a Lean function, so
  the index can be used in every expression;
* `onIcc a b depth body`: for every real `x` between the values of `a` and `b`, the condition
  `body` with `x` as its cell variable `0`. The cell variables around it move up by one
  (`push`, which is Mathlib's `Stream'.cons`).

`Cond.holds ρ c σ` is the statement over the real numbers, for the data `ρ : ι → ℝ` and the cell
variables `σ : ℕ → ℝ`. `Cond.check P benv c s` is the test: it evaluates both sides of a
comparison with `ball` and compares the balls. For `onIcc` it evaluates the two end points to
balls `A` and `B`, takes the ball `GridBall.hull A B` of the whole cell as the new cell variable
and tests `body`; if that fails and `depth` is positive, it cuts the cell at its center and
tests both halves with `depth - 1` (`bisect`).

## Main results

* `Cond.holds_of_check` (all conditions, all data, all precisions): if `benv` encloses `ρ` and
  `s` encloses `σ`, then `c.check P benv s = true` implies `c.holds ρ σ`.
* `Cond.holds_of_run`: the same for a condition without free cell variables. With the test
  `c.run P benv` it is a `Check` of the statement, `⟨c.run P benv, Cond.holds_of_run henv c σ⟩`.
* `bisect_sound` (all tests, all depths): if a test on a ball proves a property of every real
  number of the ball, then a passing bisection between two balls proves it for every real number
  between a number of the first and a number of the second.
* `exists_cell` (all sequences in a linear order, all `n > 0`): a point of `[t 0, t n]` lies in
  one of the `n` cells `[t k, t (k + 1)]`. With it, conditions on the cells of a mesh give a
  statement on the whole interval.

## Relations

`holds_of_check` is `ball_encloses` ([Ball](Ball.lean)) at both sides of each comparison, with
`EnclosesReal.le_of_leCertain`, `lt_of_ltCertain` and `eq_of_sameCertain`
([GridBallReal](../Numerics/GridBallReal.lean)), `natAll_spec` for `all`, and `bisect_sound`
with `enclosesReal_hull` for `onIcc`. `Check.all`, `Check.and` and `Check.or`
([Check](Check.lean)) are the same combinators outside the language. The NSCert checker of
BlowupZoo (`NSCert.Ex`, `NSCert.Poly.subdiv`) is the case of closed expressions and of one
polynomial on a rectangle. `coverWalk_sound` ([IntervalCover](../Numerics/IntervalCover.lean))
covers a rational interval by cells that a walk chooses; `exists_cell`, and `Check.onCover`
with it, is the cover by the cells of a given sequence of points.

## Scope

The test is sound and not complete: a true condition can fail when the precision is too small or
the cells are too coarse. An equality is decided only when both sides are computed exactly
(balls of radius zero). The cell of `onIcc` is cut only at the center of its ball, rounded to
the grid, so a cell of one grid unit does not get smaller; a pair of cell variables is bisected
one variable at a time. Cell variables are numbered from the innermost `onIcc` outward, so an
expression moved under one more `onIcc` must be renumbered by hand.
-/

@[expose] public section

namespace CAS.Cert

open CAS.Numerics CAS.Verified

/-- The environment `s` of cell variables with a new variable `0` of value `x`; the variable
`k` of `s` becomes `k + 1`. It is Mathlib's `Stream'.cons`, with the type `ℕ → α` in place of
`Stream' α`, which rewriting does not unfold. -/
abbrev push {α : Type*} (x : α) (s : ℕ → α) : ℕ → α := Stream'.cons x s

/-- The new variable `0` of `push x s` is `x`. -/
@[simp] theorem push_zero {α : Type*} (x : α) (s : ℕ → α) : push x s 0 = x := rfl

/-- The variable `k + 1` of `push x s` is the variable `k` of `s`. -/
@[simp] theorem push_succ {α : Type*} (x : α) (s : ℕ → α) (k : ℕ) : push x s (k + 1) = s k := rfl

/-- Bisection between two balls: the test `f` on the hull of `A` and `B`, or, `depth` times, on
both halves cut at the center. -/
def bisect (f : GridBall → Bool) (depth : ℕ) : GridBall → GridBall → Bool :=
  Nat.rec (motive := fun _ ↦ GridBall → GridBall → Bool)
    (fun A B ↦ f (GridBall.hull A B))
    (fun _ rec A B ↦ f (GridBall.hull A B) ||
      (rec A (GridBall.mid A B) && rec (GridBall.mid A B) B))
    depth

/-- **Soundness of bisection.** Let `f` be a test on balls such that `f B = true` proves `p x`
for every real `x` enclosed by `B`. If `A` encloses `lo`, `B` encloses `hi` and
`bisect f depth A B = true`, then `p x` holds for every real `x` with `lo ≤ x ≤ hi`.

The hull of two balls encloses everything between their numbers, and a real number lies on one
side of the center of the hull, so it lies in one of the two halves. -/
theorem bisect_sound {P : ℕ} {f : GridBall → Bool} {p : ℝ → Prop}
    (hf : ∀ (B : GridBall) (x : ℝ), B.EnclosesReal P x → f B = true → p x) :
    ∀ (depth : ℕ) (A B : GridBall) (lo hi : ℝ), A.EnclosesReal P lo → B.EnclosesReal P hi →
      bisect f depth A B = true → ∀ x, lo ≤ x → x ≤ hi → p x := by
  intro depth
  induction depth with
  | zero =>
    intro A B lo hi hA hB h x hlo hhi
    exact hf _ x (GridBall.enclosesReal_hull hA hB hlo hhi) h
  | succ d ih =>
    intro A B lo hi hA hB h x hlo hhi
    change (f (GridBall.hull A B) ||
      (bisect f d A (GridBall.mid A B) && bisect f d (GridBall.mid A B) B)) = true at h
    rcases Bool.or_eq_true_iff.mp h with h | h
    · exact hf _ x (GridBall.enclosesReal_hull hA hB hlo hhi) h
    · -- The real number at the center of the hull splits the cell in two.
      obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
      have hM := GridBall.enclosesReal_center P (GridBall.mid A B)
      rcases le_total x (((GridBall.mid A B).center : ℝ) / 2 ^ P) with hx | hx
      · exact ih A _ lo _ hA hM h1 x hlo hx
      · exact ih _ B _ hi hM hB h2 x hx hhi

/-- A condition on data indexed by `ι`. The variables of its expressions are `Sum.inl i`, the
entry `i` of the data, and `Sum.inr v`, the cell variable `v`: the variable of the `v`-th
`onIcc` around the expression, counted from the innermost, which is `0`. -/
inductive Cond (ι : Type*) where
  /-- `a ≤ b`. -/
  | le (a b : Expr (ι ⊕ ℕ))
  /-- `a < b`. -/
  | lt (a b : Expr (ι ⊕ ℕ))
  /-- `a = b`. -/
  | eq (a b : Expr (ι ⊕ ℕ))
  /-- Both conditions. -/
  | and (c d : Cond ι)
  /-- One of the two conditions. -/
  | or (c d : Cond ι)
  /-- The condition `body k` for every `k < n`. -/
  | all (n : ℕ) (body : ℕ → Cond ι)
  /-- The condition `body` for every real value, between the values of `a` and `b`, of a new
  cell variable, which is `Cond.cell 0` inside `body`; the test cuts the cell in two up to
  `depth` times. -/
  | onIcc (a b : Expr (ι ⊕ ℕ)) (depth : ℕ) (body : Cond ι)

namespace Cond

variable {ι : Type*}

/-- The entry `i` of the data, as an expression. -/
abbrev dat (i : ι) : Expr (ι ⊕ ℕ) := .var (.inl i)

/-- The cell variable `v`, as an expression: `0` is the variable of the innermost `onIcc`. -/
abbrev cell (v : ℕ) : Expr (ι ⊕ ℕ) := .var (.inr v)

/-- The statement of a condition over the real numbers, for the data `ρ` and the cell
variables `σ`. -/
def holds (ρ : ι → ℝ) : Cond ι → (ℕ → ℝ) → Prop
  | le a b, σ => a.eval (Sum.elim ρ σ) ≤ b.eval (Sum.elim ρ σ)
  | lt a b, σ => a.eval (Sum.elim ρ σ) < b.eval (Sum.elim ρ σ)
  | eq a b, σ => a.eval (Sum.elim ρ σ) = b.eval (Sum.elim ρ σ)
  | and c d, σ => holds ρ c σ ∧ holds ρ d σ
  | or c d, σ => holds ρ c σ ∨ holds ρ d σ
  | all n body, σ => ∀ k, k < n → holds ρ (body k) σ
  | onIcc a b _ body, σ => ∀ x : ℝ, a.eval (Sum.elim ρ σ) ≤ x → x ≤ b.eval (Sum.elim ρ σ) →
      holds ρ body (push x σ)

/-- The test of a condition at precision `P`, for the balls `benv` of the data and the balls
`s` of the cell variables. -/
def check (P : ℕ) (benv : ι → GridBall) : Cond ι → (ℕ → GridBall) → Bool
  | le a b, s => GridBall.leCertain (ball P (Sum.elim benv s) a) (ball P (Sum.elim benv s) b)
  | lt a b, s => GridBall.ltCertain (ball P (Sum.elim benv s) a) (ball P (Sum.elim benv s) b)
  | eq a b, s => GridBall.sameCertain (ball P (Sum.elim benv s) a) (ball P (Sum.elim benv s) b)
  | and c d, s => check P benv c s && check P benv d s
  | or c d, s => check P benv c s || check P benv d s
  | all n body, s => natAll n fun k ↦ check P benv (body k) s
  | onIcc a b depth body, s =>
      bisect (fun B ↦ check P benv body (push B s)) depth
        (ball P (Sum.elim benv s) a) (ball P (Sum.elim benv s) b)

/-- Balls for the data and for the cell variables enclose the joint environment. -/
theorem enclosesReal_elim {P : ℕ} {benv : ι → GridBall} {ρ : ι → ℝ} {s : ℕ → GridBall}
    {σ : ℕ → ℝ} (henv : ∀ i, (benv i).EnclosesReal P (ρ i))
    (hs : ∀ k, (s k).EnclosesReal P (σ k)) (w : ι ⊕ ℕ) :
    (Sum.elim benv s w).EnclosesReal P (Sum.elim ρ σ w) := by
  cases w
  · exact henv _
  · exact hs _

/-- A new cell variable with a ball and a real number of that ball keeps the enclosure. -/
theorem enclosesReal_cons {P : ℕ} {s : ℕ → GridBall} {σ : ℕ → ℝ}
    (hs : ∀ k, (s k).EnclosesReal P (σ k)) {B : GridBall} {x : ℝ}
    (hB : B.EnclosesReal P x) (k : ℕ) :
    (push B s k).EnclosesReal P (push x σ k) := by
  cases k
  · exact hB
  · exact hs _

/-- **Soundness of the test.** If the balls `benv` enclose the data `ρ` and the balls `s`
enclose the cell variables `σ`, then a passing test `c.check P benv s = true` proves the
statement `c.holds ρ σ`, for every condition `c` and every precision `P`.

This is the theorem that turns a finite computation on natural numbers into a statement about
real numbers, for every certificate written in this language. The proof is the induction over
the condition: `ball_encloses` at the leaves, `natAll_spec` for `all`, `bisect_sound` for
`onIcc`. -/
theorem holds_of_check {P : ℕ} {benv : ι → GridBall} {ρ : ι → ℝ}
    (henv : ∀ i, (benv i).EnclosesReal P (ρ i)) (c : Cond ι) :
    ∀ (s : ℕ → GridBall) (σ : ℕ → ℝ), (∀ k, (s k).EnclosesReal P (σ k)) →
      c.check P benv s = true → c.holds ρ σ := by
  induction c with
  | le a b =>
    intro s σ hs h
    exact (ball_encloses (enclosesReal_elim henv hs) a).le_of_leCertain
      (ball_encloses (enclosesReal_elim henv hs) b) h
  | lt a b =>
    intro s σ hs h
    exact (ball_encloses (enclosesReal_elim henv hs) a).lt_of_ltCertain
      (ball_encloses (enclosesReal_elim henv hs) b) h
  | eq a b =>
    intro s σ hs h
    exact (ball_encloses (enclosesReal_elim henv hs) a).eq_of_sameCertain
      (ball_encloses (enclosesReal_elim henv hs) b) h
  | and c d ihc ihd =>
    intro s σ hs h
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
    exact ⟨ihc s σ hs h1, ihd s σ hs h2⟩
  | or c d ihc ihd =>
    intro s σ hs h
    exact (Bool.or_eq_true_iff.mp h).imp (ihc s σ hs) (ihd s σ hs)
  | all n body ih =>
    intro s σ hs h k hk
    exact ih k s σ hs (natAll_spec h hk)
  | onIcc a b depth body ih =>
    intro s σ hs h x hax hxb
    -- Every ball that passes the test of `body` proves `body` at each of its real numbers.
    exact bisect_sound (p := fun x ↦ body.holds ρ (push x σ))
      (fun B y hB hf ↦ ih _ _ (enclosesReal_cons hs hB) hf) depth _ _ _ _
      (ball_encloses (enclosesReal_elim henv hs) a) (ball_encloses (enclosesReal_elim henv hs) b)
      h x hax hxb

/-- The test of a condition without free cell variables. -/
def run (P : ℕ) (benv : ι → GridBall) (c : Cond ι) : Bool :=
  c.check P benv fun _ ↦ GridBall.invalid

/-- If the balls `benv` enclose the data `ρ` and `c.run P benv = true`, then `c.holds ρ σ` for
every value `σ` of the cell variables; a condition whose cell variables are all bound by `onIcc`
does not depend on `σ`. -/
theorem holds_of_run {P : ℕ} {benv : ι → GridBall} {ρ : ι → ℝ}
    (henv : ∀ i, (benv i).EnclosesReal P (ρ i)) (c : Cond ι) (σ : ℕ → ℝ)
    (h : c.run P benv = true) : c.holds ρ σ :=
  holds_of_check henv c _ σ (fun _ ↦ GridBall.enclosesReal_of_not_ok rfl _) h

end Cond

/-- A point of `[t 0, t n]` lies in one of the cells `[t k, t (k + 1)]` with `k < n`, for every
sequence `t` in a linear order and every `n > 0`; the sequence need not be increasing. -/
theorem exists_cell {α : Type*} [LinearOrder α] {t : ℕ → α} {n : ℕ} (hn : 0 < n) {x : α}
    (h0 : t 0 ≤ x) (h1 : x ≤ t n) : ∃ k, k < n ∧ t k ≤ x ∧ x ≤ t (k + 1) := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact ⟨0, by omega, h0, h1⟩
    · rcases le_total x (t m) with hx | hx
      · obtain ⟨k, hk, hk1, hk2⟩ := ih hm hx
        exact ⟨k, by omega, hk1, hk2⟩
      · exact ⟨m, by omega, hx, h1⟩

end CAS.Cert

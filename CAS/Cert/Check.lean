/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PairChecks

/-!
# Checks: a Boolean test with the statement it proves

## Motivation

A computer-assisted proof ends in a statement `C` about real numbers and a finite computation
that establishes it. When the data of the computation are too large to appear in a theorem, the
theorem is stated for `Nonempty T`, where `T` is a type of certificates stated over the real
numbers, and a verified program gives `Nonempty T` whenever it accepts some input. What is the
one interface under which every such computation, whatever its size and whatever runs it, becomes
a proof of its statement?

## The idea

A `Check C` is a Boolean `run` together with a proof `sound` that `run = true` implies `C`. It
keeps the test and its meaning together and says nothing about how the Boolean is evaluated: by
the kernel in one module, by the kernel in many modules, by compiled code, or by a program that
reads files. Checks are assembled like the statements they prove: a conjunction of statements is
checked by the conjunction of the tests, a statement for every index below `n` by a loop, a
statement on a set by checks on finitely many cells that cover it. A checker for data of a type
`D` is a function `fun d ↦ (… : Check (C d))`.

## Main results

All definitions are general in the statement `C`.

* `Check.and`, `Check.or`, `Check.all` (`∀ k < n`), `Check.allFin` (`∀ i : Fin n`), `Check.pairs`
  (`∀ i < n, ∀ j < m`), `Check.onCover` (a statement on a set from its cells), `Check.mono`
  (a weaker statement): the combinators, each with its soundness built in.
* `Check.nonempty_of_run` (all checkers, all certificate types): if a checker for `Nonempty T`
  accepts some input, then `Nonempty T`. This is the form in which a certificate enters a final
  theorem.

## Relations

A condition `c` of the language of real expressions gives the check
`⟨c.run P benv, Cond.holds_of_run henv c σ⟩` ([Cond](Cond.lean)). `Check.all` is `natAll` with
`natAll_spec`
([MatrixPositivity](../Numerics/MatrixPositivity.lean)); `claim_of_batch_checks`
([Finite](../Numerics/Finite.lean)) is the same pattern for one family of tests on `Fin n`.
A structure of conditions is checked by `Check.and` of its fields followed by `Check.mono` with
its constructor, as in [Structure](../Examples/Cert/Structure.lean).

## Scope

A `Check` proves its statement only when `run` is known to be `true`. Nothing here evaluates it:
that is the business of `cert_eval` and of the shard commands ([Shard](Shard.lean)). A check is
data, so its test must be a program: real numbers may occur in its statement and in its proof,
and not among the arguments that the test is computed from.
-/

@[expose] public section

namespace CAS.Cert

open CAS.Numerics

/-- A Boolean test `run` whose success proves the statement `C`. -/
structure Check (C : Prop) where
  /-- The test. -/
  run : Bool
  /-- A passing test proves the statement. -/
  sound : run = true → C

namespace Check

variable {C D : Prop}

/-- A check of `C` checks every statement that `C` implies. -/
def mono (h : C → D) (c : Check C) : Check D := ⟨c.run, fun hr ↦ h (c.sound hr)⟩

/-- Both tests pass: both statements hold. -/
def and (c : Check C) (d : Check D) : Check (C ∧ D) :=
  ⟨c.run && d.run, fun h ↦
    ⟨c.sound (Bool.and_eq_true_iff.mp h).1, d.sound (Bool.and_eq_true_iff.mp h).2⟩⟩

/-- One of the two tests passes: one of the two statements holds. -/
def or (c : Check C) (d : Check D) : Check (C ∨ D) :=
  ⟨c.run || d.run, fun h ↦ (Bool.or_eq_true_iff.mp h).imp c.sound d.sound⟩

/-- The tests of the indices below `n` pass: the statement holds for every `k < n`. -/
def all {C : ℕ → Prop} (n : ℕ) (c : ∀ k, Check (C k)) : Check (∀ k, k < n → C k) :=
  ⟨natAll n fun k ↦ (c k).run, fun h _ hk ↦ (c _).sound (natAll_spec h hk)⟩

/-- The tests of all indices of `Fin n` pass: the statement holds for every `i : Fin n`. -/
def allFin {n : ℕ} {C : Fin n → Prop} (c : ∀ i, Check (C i)) : Check (∀ i, C i) :=
  ⟨natAll n fun k ↦ if h : k < n then (c ⟨k, h⟩).run else true, fun h i ↦ by
    have := natAll_spec h i.isLt
    rw [dite_eq_left i.isLt] at this
    exact (c i).sound this⟩

/-- The tests of all pairs of indices pass: the statement holds for all `i < n` and `j < m`. -/
def pairs {C : ℕ → ℕ → Prop} (n m : ℕ) (c : ∀ i j, Check (C i j)) :
    Check (∀ i, i < n → ∀ j, j < m → C i j) :=
  all n fun i ↦ all m (c i)

/-- A statement at the points of `S` from checks on the cells `cell 0, …, cell (n - 1)` that
cover them: the test of every cell passes, and every point of `S` lies in a cell. `S` and the
cells are predicates, which a test does not compute with. -/
def onCover {α : Type*} {S : α → Prop} {cell : ℕ → α → Prop} {C : α → Prop} (n : ℕ)
    (hcover : ∀ x, S x → ∃ k, k < n ∧ cell k x) (c : ∀ k, Check (∀ x, cell k x → C x)) :
    Check (∀ x, S x → C x) :=
  (all n c).mono fun h x hx ↦
    let ⟨k, hk, hxk⟩ := hcover x hx
    h k hk x hxk

/-- **A certificate from a run.** Let `c d` be a check of `Nonempty T` for every input `d`. If
the test passes for some input, then `Nonempty T`.

This is the form in which a certificate that is too large for a theorem statement is used: the
final theorem assumes `Nonempty T` for a type `T` of certificates stated over the real numbers,
and the verified checker supplies it from any accepted input. The input is quantified
existentially, so nothing has to be known about it except that the test passed. -/
theorem nonempty_of_run {D : Type*} {T : Sort*} (c : D → Check (Nonempty T))
    (h : ∃ d, (c d).run = true) : Nonempty T :=
  let ⟨d, hd⟩ := h
  (c d).sound hd

end Check

end CAS.Cert

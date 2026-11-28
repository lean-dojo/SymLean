/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Cert.Cond
public import CAS.Numerics.Finite

/-!
# Ranges of a family of tests

## Motivation

A certificate with many indices is a family of tests `t : ℕ → Bool` and the statement that
`t i = true` for every `i < N`. When one kernel evaluation of all of them is too long, the
indices are cut into ranges, each range is one evaluation, possibly in a module of its own, and
the ranges are joined. Which statement does one range prove, so that joining needs no further
computation?

## The idea

One range is one loop: `natAll count fun k ↦ t (start + k)` is a closed Boolean that the kernel
or compiled code evaluates. `rangeAll_of_natAll` reads a passing loop back as
`RangeAll (fun j : Fin N ↦ t j.val = true) start count`, the range statement of
[Finite](../Numerics/Finite.lean), whose lemmas `rangeAll_append` and `forall_of_rangeAll` join
adjacent ranges into `∀ j : Fin N, t j.val = true`.

## Main results

For all families of tests and all ranges:

* `rangeAll_of_natAll`: a passing loop of `t` over `start, …, start + count - 1`, with
  `start + count ≤ n`, proves the range statement of `t`.
* `natAll_eq_true_iff`: a loop passes exactly when its tests pass at every index. One direction
  is `natAll_spec`.

## Relations

`rangeAll_of_natAll` is `natAll_range_spec` ([PairChecks](../Numerics/PairChecks.lean)) at
every index of the range. The commands `cert_shard` and `cert_aggregate` ([Shard](Shard.lean))
state and join the ranges. `natAll_eq_true_iff` turns the joined ranges back into the test of
a `Check`, as in `MeshSpec.checker_run` ([MeshSpec](../Examples/Cert/MeshSpec.lean)).

## Scope

The ranges are consecutive indices of one family. A family over pairs of indices is cut by
numbering the pairs.
-/

@[expose] public section

namespace CAS.Cert

open CAS.Numerics

/-- **A loop proves a range.** If the loop `natAll count fun k ↦ t (start + k)` passes and
`start + count ≤ n`, then `t j = true` on the `count` indices from `start`, as the range
statement `RangeAll (fun j : Fin n ↦ t j.val = true) start count`. The loop is the only
computation of a range. -/
theorem rangeAll_of_natAll {n start count : ℕ} {t : ℕ → Bool} (hbound : start + count ≤ n)
    (h : natAll count (fun k ↦ t (start + k)) = true) :
    RangeAll (fun j : Fin n ↦ t j.val = true) start count := fun j ↦
  ⟨Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt start) hbound,
    natAll_range_spec h (Nat.le_add_right start j.val) (Nat.add_lt_add_left j.isLt start)⟩

/-- **A loop passes exactly when its tests do.** `natAll n t = true` if and only if
`t k = true` for every `k < n`. The direction from the loop is `natAll_spec`; the other one
turns the joined ranges back into one Boolean, the `run` of a checker. -/
theorem natAll_eq_true_iff {n : ℕ} {t : ℕ → Bool} :
    natAll n t = true ↔ ∀ k, k < n → t k = true := by
  refine ⟨fun h _ hk ↦ natAll_spec h hk, fun h ↦ ?_⟩
  induction n with
  | zero => rfl
  | succ m ih =>
    exact Bool.and_eq_true_iff.mpr ⟨h m (Nat.lt_succ_self m), ih fun k hk ↦ h k (by omega)⟩

end CAS.Cert

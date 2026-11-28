/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.CEGA

/-!
# A reusable cosine enclosure

On `[-1/10, 1/10]`, CEGA proves `199/200 ≤ cos x ≤ 1`. We store the
bound in a certificate so a later proof can reuse it without evaluating cosine again: as it is
(`cosine_enclosed`), with wider endpoints (`cosine_enclosed_wider`) and on a smaller set
(`cosine_enclosed_on`). Tighter endpoints are refused. A bound certificate made from it is
weakened to a larger bound (`cosine_le_two`), and so is a certificate that a rule builds from it
(`cosine_sub_enclosed`).
-/

@[expose] public noncomputable section

namespace CAS.Examples.Numerics.CosineEnclosure

open CAS.Certificate

/-- The interval on which the cosine bound holds. -/
def domain : Set ℝ := Set.Icc (-1 / 10 : ℝ) (1 / 10 : ℝ)

/-- A cosine enclosure proved once and available to later bounds. -/
def cosineEnclosure : EnclosureCert ℝ domain where
  fn := Real.cos
  lo := 199 / 200
  hi := 1
  sound := by
    intro x hx
    change x ∈ Set.Icc (-1 / 10 : ℝ) (1 / 10 : ℝ) at hx
    constructor <;> cega

/-- Project the stored certificate to an ordinary two-sided bound. -/
theorem cosine_enclosed : EnclosedOn Real.cos domain (199 / 200 : ℝ) 1 := by
  cega using cosineEnclosure

/-- Wider endpoints: `cega using` widens the stored certificate and proves the two comparisons
`0 ≤ 199 / 200` and `1 ≤ 2` by arithmetic. -/
theorem cosine_enclosed_wider : EnclosedOn Real.cos domain (0 : ℝ) 2 := by
  cega using cosineEnclosure

/-- On a smaller set with wider endpoints, the certificate is restricted and then widened. -/
theorem cosine_enclosed_on (s : Set ℝ) (hs : s ⊆ domain) : EnclosedOn Real.cos s (0 : ℝ) 2 := by
  cega using cosineEnclosure

/-- Tighter endpoints are refused: the certificate does not prove them. -/
example : True := by
  fail_if_success
    have : EnclosedOn Real.cos domain (999 / 1000 : ℝ) 1 := by cega using cosineEnclosure
  trivial

/-- The upper end of the enclosure as a bound certificate of its own. -/
def cosineBound : BoundCert ℝ domain := .ofEnclosure cosineEnclosure

/-- A larger bound: `cega using` weakens the bound certificate, whose number `1` it reads off
`BoundCert.ofEnclosure cosineEnclosure`. -/
theorem cosine_le_two : BoundOn Real.cos domain 2 := by
  cega using cosineBound

/-- A certificate built by a rule: `cosineEnclosure.sub cosineEnclosure` encloses
`cos x - cos x` in `[199 / 200 - 1, 1 - 199 / 200]`, and `cega using` widens it to `[-1, 1]`. The
two ends are differences of fields, which are read inside the difference. -/
theorem cosine_sub_enclosed :
    EnclosedOn (fun x ↦ Real.cos x - Real.cos x) domain (-1 : ℝ) 1 := by
  cega using cosineEnclosure.sub cosineEnclosure

end CAS.Examples.Numerics.CosineEnclosure

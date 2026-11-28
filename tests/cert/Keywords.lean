/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
import CAS
import CAS.Cert.Reduce

/-!
# The certificate tactics reserve no word of other tactics

`cert_cond p depth d` and `cert_reduce name (leaving := [f]) : S` read the words `depth` and
`leaving`. A word that a syntax declares without `&` becomes a keyword in every file that
imports the module, so `cega (depth := n)` and a variable named `depth` would stop parsing after
`import CAS.Cert.Reduce`. This file imports both and elaborates all of them;
`tests/cert/run.sh` runs it.
-/

open CAS.Cert

-- The option `depth` of `cega`, next to the certificate tactics.
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 3 / 10 := by
  cega (depth := 2)

-- The word `depth` of `cert_cond`.
example : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → x ^ 2 ≤ 1 + 1 / 1000 := by cert_cond 64 depth 3

-- Both words as names.
example : ℕ → ℕ := fun depth ↦ depth
example : ℕ → ℕ := fun leaving ↦ leaving

-- The named argument `depth` of `Cond.onIcc`.
example : Cond Empty := .onIcc (.nat 0) (.nat 1) (depth := 2) (.le (Cond.cell 0) (.nat 1))

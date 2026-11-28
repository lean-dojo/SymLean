/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Inclusion.Basic
public meta import CAS.Continuum.Interval.Inclusion.Basic
public import FloatLib.Numerics.Enclosure.Expression.Real
public import Mathlib.Tactic.Inclusion.ExtensionAPI.Attr
import FloatLib.Numerics.Enclosure.Expression.ElementaryTableProof
import FloatLib.Numerics.Enclosure.Expression.StandardProof
import FloatLib.Numerics.Enclosure.Interval.ExactProof
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# `cega_real` operations

We extend Mathlib's `interval_dyadic_real` family with the `cega_real` operations for
reciprocals and quotients, natural powers, `π`, `exp`, `log`, `sqrt`, `sin`, `cos`, `arctan`,
`arcsin`, `arccos`, `sinh`, `cosh` and `tanh`. For example:

```
example : Real.exp 1 < 2.7183 := by dyadic_interval [cega_real, prec := 20]
```

The reciprocal and the powers are FloatLib's exact interval operations, and `π` is FloatLib's
Machin enclosure `Backend.piBounds prec`, narrower than `2 ^ (-prec)`. Every other operation is
FloatLib's elementary table `Backend.elementaryWith` at the settings `settings prec`, with the
sharp sine and cosine and the total square root, logarithm, arcsine and arccosine. The reciprocal
takes the whole line as its range on an argument interval that contains zero, which holds Lean's
`0⁻¹ = 0`. The logarithm follows Mathlib's `log x = log |x|` with `log 0 = 0`, so it takes the
whole line only on an argument interval that contains zero and another point.

`dyadic_interval` evaluates the interval program it builds before the kernel checks it, so the
ranges must also be available at compile time. The `meta` import above makes them available to
every module that imports this one.

The `prec` parameter sets the dyadic rounding of every result and also the work FloatLib does
before rounding: `π` is enclosed to `2 ^ (-prec)`, the Taylor order of `exp`, `sinh`, `cosh` and
`tanh` and the number of series terms of `log` are at least `prec / 2`, and the square root keeps
at least `prec + 4` binary digits. The trigonometric and inverse trigonometric series keep their
fixed degrees, so increasing `prec` alone does not refine them.

## Main results

* `mem_liftElementary`: every operation of the table, lifted at any precision, encloses its real
  function, given a fallback that contains every value.
* `inv_mem`, `div_mem`, `pow_mem`, `pi_mem`, `exp_mem` to `tanh_mem`: the `cega_real` operations.
-/

@[expose] public section

open Inclusion
open Inclusion.IntervalDyadicReal (Dyadic.toReal)

namespace CAS.Continuum.CEGAInclusion

open FloatLib.Numerics.Interval (UnaryOp)
open FloatLib.Numerics.Interval.Backend (containsReal_elementaryWith piBounds containsReal_piBounds)
open FloatLib.Numerics.Interval.Exact (powNat containsReal_powNat containsReal_inv)

/-! ## Global ranges -/

/-- Every real number lies in the unbounded dyadic interval `Interval.univ Dyadic`. -/
theorem mem_univ (x : ℝ) : x ∈ Interval.univ Dyadic :=
  Interval.mem_map_univ Dyadic.toReal x

/-- The dyadic `1` read as a real is `1`. -/
theorem toReal_one : Dyadic.toReal 1 = 1 := by
  simp [Dyadic.toReal, show (1 : Dyadic).toRat = 1 from rfl]

/-- Reading dyadics as reals commutes with negation: `toReal (-d) = -toReal d`. -/
theorem toReal_neg (d : Dyadic) : Dyadic.toReal (-d) = -Dyadic.toReal d := by
  simp [Dyadic.toReal, Dyadic.toRat_neg]

/-- A real `x` with `-1 ≤ x ≤ 1` lies in the dyadic interval `closed (-1) 1`. -/
theorem mem_closed_neg_one_one {x : ℝ} (hlo : -1 ≤ x) (hhi : x ≤ 1) : x ∈ closed (-1) 1 :=
  mem_closed (by simpa [toReal_neg, toReal_one] using hlo) (by simpa [toReal_one] using hhi)

/-- A real `x` with `-2 ≤ x ≤ 2` lies in the dyadic interval `closed (-2) 2`. -/
theorem mem_closed_neg_two_two {x : ℝ} (hlo : -2 ≤ x) (hhi : x ≤ 2) : x ∈ closed (-2) 2 :=
  mem_closed (by simpa [toReal_neg] using hlo) (by simpa using hhi)

/-- Every operation `op` of FloatLib's elementary table, lifted at any precision, encloses its
real function `g = op.eval` on dyadic intervals, when `fallback` contains every value of `g`. -/
theorem mem_liftElementary {op : UnaryOp} {g : ℝ → ℝ} {fallback : Interval Dyadic}
    (hfallback : ∀ x, g x ∈ fallback) {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) {prec : ℕ}
    (hg : op.eval = g := by rfl) : g x ∈ liftElementary op fallback I prec := by
  subst hg
  exact mem_liftUnary (fun h hJ ↦ containsReal_elementaryWith _ h hJ) hfallback hx prec

/-! ## Arithmetic -/

/-- If `invRange? J = some K` (so `J` lies on one side of zero) and `x` lies in `J`, then `x⁻¹` lies
in `K`. -/
theorem invRange?_sound {J K : FloatLib.Numerics.Interval ℚ} {x : ℝ} (hK : invRange? J = some K)
    (hx : J.ContainsReal some x) : K.ContainsReal some x⁻¹ := by
  unfold invRange? at hK
  split_ifs at hK with h
  cases hK
  exact containsReal_inv h hx

/-- The reciprocal range of `I`, with the whole line as the fallback when `I` is unbounded or
contains zero. -/
@[inclusion_op cega_real]
theorem inv_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    x⁻¹ ∈ liftUnary invRange? (Interval.univ Dyadic) I prec :=
  mem_liftUnary invRange?_sound (fun _ ↦ mem_univ _) hx prec

/-- A quotient is the product with the reciprocal range. -/
@[inclusion_op cega_real]
theorem div_mem {x y : ℝ} {I J : Interval Dyadic} (hx : x ∈ I) (hy : y ∈ J) (prec : ℕ) :
    x / y ∈ I.mul (liftUnary invRange? (Interval.univ Dyadic) J prec) :=
  div_eq_mul_inv x y ▸ IntervalDyadicReal.mul_mem hx (inv_mem hy prec)

/-- Natural powers through FloatLib's exact power, with its sharp odd and even endpoint bounds. -/
@[inclusion_op cega_real]
theorem pow_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (n : ℕ) (prec : ℕ) :
    x ^ n ∈ liftUnary (fun J ↦ some (powNat J n)) (Interval.univ Dyadic) I prec :=
  mem_liftUnary (by rintro J K y ⟨⟩ hy; exact containsReal_powNat n hy) (fun _ ↦ mem_univ _)
    hx prec

/-- `π` from FloatLib's Machin enclosure, narrower than `2 ^ (-prec)`. -/
@[inclusion_op cega_real]
theorem pi_mem (prec : ℕ) : Real.pi ∈ ofRational (piBounds prec) prec :=
  mem_ofRational (containsReal_piBounds prec) prec

/-! ## Exponential, logarithm, and square root -/

/-- The exponential range of `I`, with `[0, ∞)` as the unbounded-input fallback. -/
@[inclusion_op cega_real]
theorem exp_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.exp x ∈ liftElementary .exp (atLeast 0) I prec :=
  mem_liftElementary (fun y ↦ mem_atLeast (by simpa [Dyadic.toReal] using (Real.exp_pos y).le)) hx

/-- The total logarithm range of `I`, with the whole line as the fallback on an interval that
contains zero and another point. -/
@[inclusion_op cega_real]
theorem log_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.log x ∈ liftElementary .log (Interval.univ Dyadic) I prec :=
  mem_liftElementary (fun _ ↦ mem_univ _) hx

/-- The total square-root range of `I`, including Mathlib's zero values below zero. -/
@[inclusion_op cega_real]
theorem sqrt_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.sqrt x ∈ liftElementary .sqrt (atLeast 0) I prec :=
  mem_liftElementary (fun _ ↦ mem_atLeast (by simp [Dyadic.toReal])) hx

/-! ## Trigonometric functions and their inverses -/

/-- The sharp sine range of `I`, with the global bound `[-1, 1]` for unbounded inputs. -/
@[inclusion_op cega_real]
theorem sin_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.sin x ∈ liftElementary .sin (closed (-1) 1) I prec :=
  mem_liftElementary (fun y ↦ mem_closed_neg_one_one (Real.neg_one_le_sin y) (Real.sin_le_one y)) hx

/-- The sharp cosine range of `I`, with the global bound `[-1, 1]` for unbounded inputs. -/
@[inclusion_op cega_real]
theorem cos_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.cos x ∈ liftElementary .cos (closed (-1) 1) I prec :=
  mem_liftElementary (fun y ↦ mem_closed_neg_one_one (Real.neg_one_le_cos y) (Real.cos_le_one y)) hx

/-- The arctangent range of `I`, with `[-2, 2]` containing every fallback value. -/
@[inclusion_op cega_real]
theorem arctan_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.arctan x ∈ liftElementary .atan (closed (-2) 2) I prec :=
  mem_liftElementary (fun y ↦ mem_closed_neg_two_two
      (by linarith [Real.neg_pi_div_two_lt_arctan y, Real.pi_div_two_le_two])
      (by linarith [Real.arctan_lt_pi_div_two y, Real.pi_div_two_le_two])) hx

/-- The total arcsine range of `I`, with `[-2, 2]` containing every fallback value. -/
@[inclusion_op cega_real]
theorem arcsin_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.arcsin x ∈ liftElementary .asin (closed (-2) 2) I prec :=
  mem_liftElementary (fun y ↦ mem_closed_neg_two_two
      (by linarith [Real.neg_pi_div_two_le_arcsin y, Real.pi_div_two_le_two])
      (by linarith [Real.arcsin_le_pi_div_two y, Real.pi_div_two_le_two])) hx

/-- The total arccosine range of `I`, with `[0, 4]` containing every fallback value. -/
@[inclusion_op cega_real]
theorem arccos_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.arccos x ∈ liftElementary .acos (closed 0 4) I prec :=
  mem_liftElementary
    (fun y ↦ mem_closed (by simpa [Dyadic.toReal] using Real.arccos_nonneg y)
      (by simpa using (Real.arccos_le_pi y).trans Real.pi_le_four)) hx

/-! ## Hyperbolic functions -/

/-- The hyperbolic sine range of `I`, falling back to the whole line on unbounded inputs. -/
@[inclusion_op cega_real]
theorem sinh_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.sinh x ∈ liftElementary .sinh (Interval.univ Dyadic) I prec :=
  mem_liftElementary (fun _ ↦ mem_univ _) hx

/-- The hyperbolic cosine range of `I`, with the global lower bound one as the fallback. -/
@[inclusion_op cega_real]
theorem cosh_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.cosh x ∈ liftElementary .cosh (atLeast 1) I prec :=
  mem_liftElementary (fun y ↦ mem_atLeast (by rw [toReal_one]; exact Real.one_le_cosh y)) hx

/-- The hyperbolic tangent range of `I`, with the global bound `[-1, 1]` as the fallback. -/
@[inclusion_op cega_real]
theorem tanh_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.tanh x ∈ liftElementary .tanh (closed (-1) 1) I prec :=
  mem_liftElementary
    (fun y ↦ mem_closed_neg_one_one (Real.neg_one_lt_tanh y).le (Real.tanh_lt_one y).le) hx

end CAS.Continuum.CEGAInclusion

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.DecimalCheck
public import CAS.Expr.FloatLib
public import FloatLib.Numerics.Enclosure.Expression.ElementaryTableProof
public import FloatLib.Numerics.Enclosure.Expression.StandardProof
public import FloatLib.Numerics.Enclosure.Interval.RoundingProof

/-!
# Interval evaluation at a requested precision

`DigitsEval.eval` encloses the value of a verified expression with FloatLib's interval arithmetic
at a precision `p` that the caller chooses. The expression is translated into FloatLib's
expression language, each occurrence of a variable becoming an input of its own with the interval
of that variable, and the translation is evaluated on `p.backend`, a FloatLib backend with
rational ends. Every operation of that backend is sound at every precision, so `eval_sound` holds
with no condition on the precision. The checks `lowerCheck`, `upperCheck` and `enclosureCheck`
compare the evaluated interval of a closed expression with rational bounds. They are closed
Boolean propositions for the kernel, and `of_lowerCheck_decimal` and `of_upperCheck_decimal`
state the decimal digits they certify.

## Main definitions

* `DigitsEval.Precision`: the grid bits and the two series lengths of one evaluation.
* `DigitsEval.Precision.backend`: FloatLib's backend at a precision. It is `Precision.base`, which
  rounds with FloatLib's outward roundings and takes the elementary functions from FloatLib's table
  at the setting `Precision.toSetting`, with the registered calls `π`, the real power and `e` at
  the accuracy `Precision.toConfig`.
* `DigitsEval.piInterval`: FloatLib's enclosure of `π` at `w` bits.
* `DigitsEval.bounds?`, `DigitsEval.eval`: FloatLib's enclosure of an expression on an
  environment of rational intervals, and the same enclosure as a `RationalInterval`.
* `DigitsEval.evalOn`: the evaluator on a one-variable expression and an interval, with a
  fallback. `DigitsEval.sin`, `cos`, `asin` and `acos` are its instances.
* `DigitsEval.lowerCheck`, `DigitsEval.upperCheck`, `DigitsEval.enclosureCheck`: the evaluated
  interval of a closed expression lies in `[lo, hi)`, in `(lo, hi]` or in `[lo, hi]`.

## Main results

* `DigitsEval.Precision.base_sound`, `DigitsEval.Precision.backend_sound`: the backend is sound at
  every precision.
* `DigitsEval.piInterval_sound`: `piInterval w` contains `π` for every `w`.
* `DigitsEval.containsReal_bounds?`, `DigitsEval.eval_sound`: at every precision and for every
  expression, a successful evaluation encloses the real value when the environment encloses the
  point.
* `DigitsEval.of_lowerCheck_decimal`, `DigitsEval.of_upperCheck_decimal`,
  `DigitsEval.of_lowerCheck_scaled`, `DigitsEval.of_upperCheck_scaled`,
  `DigitsEval.of_enclosureCheck`, `DigitsEval.of_enclosureCheck_decimal`: a check that
  evaluates to `true` gives the stated bounds on the value of the closed expression.

## Implementation notes

Constants, the intervals of the variables and the results of the algebraic operations are rounded
outward to the grid `2 ^ (-p.bits)`. Quotients and reciprocals are rounded on a grid that follows
their magnitude, so a small quotient such as `1 / 10 ^ 30` keeps about `p.bits` significant bits.
The elementary functions come from FloatLib's table `Backend.elementaryWith` at the setting
`p.toSetting`, and their results are rounded on the grid of `p.bits` bits. The exponential and the
logarithm are FloatLib's binary-grid point kernels at the two ends of a monotone range, with
`p.terms` and `p.logTerms` series terms on the grid of `p.bits` bits. Sine, cosine, arctangent
and the inverse sine and cosine use `p.terms` terms, and square roots, those inside the inverse
sine and cosine included, the grid of `p.bits` bits. `π`, the real power `a ^ b` and `e` are
FloatLib's registered calls, with their results rounded on the same grid: four times FloatLib's
Machin enclosure of `π / 4`, of width below `2 ^ (-p.bits)`; `exp (log a * b)` on a base interval
with a positive lower end, at the degree `p.logTerms`; and FloatLib's enclosure of the exponential
at `1`, at the degree `p.bits / 2 + 1`.

The translation writes the argument of the square root as `max 0 a` and those of the inverse sine
and cosine as `max (-1) (min 1 a)`, which keeps the values of Mathlib's total functions. The
evaluation has FloatLib's zero rule, so `0 * (1 / x)` has an enclosure even where `1 / x` has
none. The result is read back as a `RationalInterval`, whose ends are ordered because it contains
the value of the expression at the lower ends of the environment, so no comparison is computed
for the order.

`#cas [N d]` (`CAS.Command.Digits`) runs the evaluator outside the kernel at up to five precisions,
doubling bits and terms each time, until the enclosure fixes the requested digits. The kernel then
decides the corresponding check instance without native code (`decideClosedCertificate`), and
`of_lowerCheck_decimal` or one of its variants turns it into the stated bounds. The precision
decides only whether a check succeeds, never whether it is sound. The kernel decides the checks by
plain reduction, so a faster definition in FloatLib makes them faster, while a rewrite rule of
FloatLib's `@[kernel_optimize]` set does not reach them.

## References

* Ramon E. Moore, R. Baker Kearfott and Michael J. Cloud, *Introduction to Interval Analysis*,
  SIAM, Philadelphia, 2009, <https://doi.org/10.1137/1.9780898717716>. Chapter 3 for outwardly
  rounded interval arithmetic.
* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, 2026, <https://github.com/lean-dojo/FloatLib>. We use its backend
  `Backend.ofRoundings` with its outward roundings, its elementary table `Backend.elementaryWith`,
  its registered calls `Backend.Standard.extensions`, and its evaluation `Expr.evalZero?` with the
  containment theorem `Expr.containsReal_evalZero?`.
-/

@[expose] public section

namespace CAS.Continuum
namespace DigitsEval

open FloatLib.Numerics.Interval FloatLib.Numerics.Interval.Backend
open RationalInterval

/-- The working precision of the evaluator: the rounding grid and the series lengths. -/
structure Precision where
  /-- Results are rounded outward to the grid `2 ^ (-bits)`. -/
  bits : ℕ
  /-- Number of series terms of the exponential, the trigonometric functions and their
  inverses. -/
  terms : ℕ
  /-- Number of series terms of the logarithm, which gains about half a digit per term. -/
  logTerms : ℕ
  deriving Repr, DecidableEq

/-- The working precision for about `digits` decimal digits: a grid of `3.322 digits + 40`
bits and series lengths that reach it for arguments of moderate size. -/
def precisionFor (digits : ℕ) : Precision :=
  { bits := digits * 3322 / 1000 + 40, terms := digits + 24,
    logTerms := digits * 22 / 10 + 40 }

namespace Precision

/-- The setting of FloatLib's elementary table at precision `p`: `p.logTerms` series terms for the
logarithm and `p.terms` for every other function, square roots on the grid of `p.bits` bits, and
the exponential and the logarithm by FloatLib's binary-grid kernels on that grid. -/
def toSetting (p : Precision) : ElementarySettings where
  expDegree := p.terms
  logDegree := p.logTerms
  trigDegree := p.terms
  atanDegree := p.terms
  inverseTrigDegree := p.terms
  hyperbolicDegree := p.terms
  precision := p.bits
  gridExpLog := some p.bits

/-- The accuracy settings of FloatLib's registered calls at precision `p`: `π` to `p.bits` bits,
the real power at the degree `p.logTerms` of the logarithm, and `e` at the degree
`p.bits / 2 + 1` of the exponential. -/
def toConfig (p : Precision) : Backend.Config where
  precision := p.bits
  degree := p.logTerms

/-- FloatLib's backend at precision `p` without registered calls, with rational ends: algebraic
results rounded outward to the grid `2 ^ (-p.bits)`, quotients and reciprocals on a grid that keeps
about `p.bits` significant bits, and FloatLib's elementary table at `p.toSetting`, with its results
on the grid of `p.bits` bits. -/
def base (p : Precision) : Backend ℚ :=
  ofRoundings (FloatLib.Numerics.OutwardRounding.grid p.bits)
    (FloatLib.Numerics.OutwardRounding.quotient p.bits)
    (FloatLib.Numerics.OutwardRounding.grid p.bits) (elementaryWith p.toSetting)

/-- The backend `p.base` is sound at every precision. -/
theorem base_sound (p : Precision) : p.base.Sound :=
  ofRoundings_sound (FloatLib.Numerics.OutwardRounding.grid p.bits)
    (FloatLib.Numerics.OutwardRounding.quotient p.bits)
    (FloatLib.Numerics.OutwardRounding.grid p.bits) _ rfl rfl
    (containsReal_elementaryWith p.toSetting)

/-- FloatLib's backend at precision `p`: `p.base` with the registered calls `π`, the real power
and `e` at the accuracy `p.toConfig`. -/
def backend (p : Precision) : Backend ℚ :=
  p.base.withExtensions p.toConfig Standard.extensions

/-- The backend at every precision is sound, with `π`, the real power and `e` as its calls. -/
theorem backend_sound (p : Precision) : p.backend.Sound (extensionValues Standard.functions) :=
  withExtensions_sound p.base_sound _ Standard.extensions_sound

end Precision

/-- `π` to `w` bits: FloatLib's enclosure `Backend.piBounds w`, four times its Machin enclosure of
`π / 4`, of width below `2 ^ (-w)` (`Backend.piBounds_width_lt`). It is the enclosure of the
registered call `π` at the precision `w`. -/
def piInterval (w : ℕ) : RationalInterval :=
  ofFloatLib (piBounds w) (piBounds_lo_le_hi w)

/-- `piInterval w` contains `π` for every `w`. -/
theorem piInterval_sound (w : ℕ) : (piInterval w).MemReal Real.pi :=
  (memReal_ofFloatLib_iff _ _ _).mpr (containsReal_piBounds w)

variable {ι : Type*}

/-- FloatLib's enclosure of `expr` at precision `p` on the environment `env`, as an interval with
rational ends. The intervals of the variable occurrences of `expr` are rounded outward by
`p.backend`, the expression with its occurrences numbered (`Verified.Expr.numberOccurrences`) is
translated and evaluated on them with the zero rule (`Expr.evalZero?`), and the two ends of the
result are read back. It is `none` when an operation has no enclosure, such as a quotient by an
interval that contains zero or a logarithm of one that reaches zero. -/
def bounds? (p : Precision) (env : ι → RationalInterval) (expr : Verified.Expr ι) :
    Option (FloatLib.Numerics.Interval ℚ) := do
  let intervals ← Box.enclose? (expr.occurrences.map fun i ↦ (env i).toFloatLib) p.backend
  let I ← ((expr.numberOccurrences 0).toFloatLib id).evalZero? p.backend
    (FloatLib.Numerics.Kernel.Seq.nth? intervals)
  I.decode? p.backend.decode

/-- The enclosure `bounds? p env expr` contains the value of `expr` at every point `ρ` that the
environment encloses. -/
theorem containsReal_bounds? {p : Precision} {env : ι → RationalInterval} {ρ : ι → ℝ}
    (henv : ∀ i, (env i).MemReal (ρ i)) {expr : Verified.Expr ι}
    {J : FloatLib.Numerics.Interval ℚ} (h : bounds? p env expr = some J) :
    J.ContainsReal some (expr.eval ρ) := by
  simp only [bounds?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨intervals, hbox, I, heval, hdecode⟩ := h
  have hreal := Verified.Expr.containsReal_occurrences (intervals := fun i ↦ (env i).toFloatLib)
    (expr := expr) fun i _ ↦ ((env i).toFloatLib_containsReal_iff _).mpr (henv i)
  have hI := Verified.Expr.containsReal_evalZero?_numberOccurrences p.base_sound (fun k K hK ↦ by
    rw [FloatLib.Numerics.Kernel.Seq.nth?_eq] at hK
    exact Box.containsReal_enclose? p.backend_sound hbox hreal k K hK) heval
  exact (containsReal_some_iff _ _).mpr ((containsReal_iff_of_decode? hdecode _).mp hI)

/-- Interval evaluation of a verified expression at precision `p`: `bounds? p env expr` with its
ends ordered, since it contains the value of `expr` at the lower ends of `env`. -/
def eval (p : Precision) {ι : Type*} (env : ι → RationalInterval) (expr : Verified.Expr ι) :
    Option RationalInterval :=
  match h : bounds? p env expr with
  | some J => some (ofFloatLib J (ordered_of_containsReal
      (containsReal_bounds? (ρ := fun i ↦ ((env i).lo : ℝ)) (fun i ↦ (env i).lo_memReal) h)))
  | none => none

/-- A successful evaluation encloses the real value whenever the environment encloses the
point. -/
theorem eval_sound (p : Precision) {ι : Type*} (env : ι → RationalInterval) (ρ : ι → ℝ)
    (henv : ∀ i, (env i).MemReal (ρ i)) (expr : Verified.Expr ι) {I : RationalInterval}
    (h : eval p env expr = some I) : I.MemReal (expr.eval ρ) := by
  unfold eval at h
  split at h
  · rename_i J hJ
    cases h
    exact (memReal_ofFloatLib_iff _ _ _).mpr (containsReal_bounds? henv hJ)
  · cases h

/-- The enclosure of the one-variable expression `expr` on the interval `I` at precision `p`
(`eval`), and `fallback` where `eval` has none. -/
def evalOn (p : Precision) (expr : Verified.Expr (Fin 1)) (fallback I : RationalInterval) :
    RationalInterval :=
  (eval p (fun _ ↦ I) expr).getD fallback

/-- If `x` lies in `I` and `fallback` contains the value of `expr` at `x`, then so does
`evalOn p expr fallback I`. -/
theorem evalOn_sound (p : Precision) {expr : Verified.Expr (Fin 1)} {fallback I : RationalInterval}
    {x : ℝ} (hx : I.MemReal x) (hfallback : fallback.MemReal (expr.eval fun _ ↦ x)) :
    (evalOn p expr fallback I).MemReal (expr.eval fun _ ↦ x) := by
  unfold evalOn
  cases h : eval p (fun _ ↦ I) expr with
  | none => exact hfallback
  | some J => exact eval_sound p _ (fun _ ↦ x) (fun _ ↦ hx) expr h

/-- The sine on `I` at precision `p`: `eval` of `sin x`, which is FloatLib's sine enclosure with
`p.terms` terms rounded outward to `p.bits` bits, and `[-1, 1]` where `eval` has none. -/
def sin (p : Precision) (I : RationalInterval) : RationalInterval :=
  evalOn p (.sin (.var 0)) negOneOne I

/-- At every precision `p`, if `x` lies in `I` then `sin x` lies in `sin p I`. -/
theorem sin_sound (p : Precision) {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    (sin p I).MemReal (Real.sin x) :=
  evalOn_sound p hx ⟨by simpa [negOneOne] using Real.neg_one_le_sin x,
    by simpa [negOneOne] using Real.sin_le_one x⟩

/-- The cosine on `I` at precision `p`: `eval` of `cos x`, which is FloatLib's cosine enclosure
with `p.terms` terms rounded outward to `p.bits` bits, and `[-1, 1]` where `eval` has none. -/
def cos (p : Precision) (I : RationalInterval) : RationalInterval :=
  evalOn p (.cos (.var 0)) negOneOne I

/-- At every precision `p`, if `x` lies in `I` then `cos x` lies in `cos p I`. -/
theorem cos_sound (p : Precision) {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    (cos p I).MemReal (Real.cos x) :=
  evalOn_sound p hx ⟨by simpa [negOneOne] using Real.neg_one_le_cos x,
    by simpa [negOneOne] using Real.cos_le_one x⟩

/-- The inverse sine on `I` at precision `p`: `eval` of `arcsin x`, which is FloatLib's enclosure
on `I` clamped to `[-1, 1]`, with `p.terms` series terms and square roots on the grid of `p.bits`
bits, and `[-2, 2]` where `eval` has none. -/
def asin (p : Precision) (I : RationalInterval) : RationalInterval :=
  evalOn p (.asin (.var 0)) (ofBounds (-2) 2 (by norm_num)) I

/-- At every precision `p`, if `x` lies in `I` then `Real.arcsin x` lies in `asin p I`. -/
theorem asin_sound (p : Precision) {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    (asin p I).MemReal (Real.arcsin x) := by
  refine evalOn_sound p hx ⟨?_, ?_⟩ <;> simp only [ofBounds, Verified.Expr.eval] <;> push_cast
  · linarith [Real.neg_pi_div_two_le_arcsin x, Real.pi_le_four]
  · linarith [Real.arcsin_le_pi_div_two x, Real.pi_le_four]

/-- The inverse cosine on `I` at precision `p`: `eval` of `arccos x`, which is FloatLib's
enclosure on `I` clamped to `[-1, 1]`, with `p.terms` series terms and square roots on the grid
of `p.bits` bits, and `[0, 4]` where `eval` has none. -/
def acos (p : Precision) (I : RationalInterval) : RationalInterval :=
  evalOn p (.acos (.var 0)) (ofBounds 0 4 (by norm_num)) I

/-- At every precision `p`, if `x` lies in `I` then `Real.arccos x` lies in `acos p I`. -/
theorem acos_sound (p : Precision) {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    (acos p I).MemReal (Real.arccos x) := by
  refine evalOn_sound p hx ⟨?_, ?_⟩ <;> simp only [ofBounds, Verified.Expr.eval] <;> push_cast
  · exact Real.arccos_nonneg x
  · linarith [Real.arccos_le_pi x, Real.pi_le_four]

/-- The environment of a closed expression. -/
def closedEnv : Fin 0 → RationalInterval := Fin.elim0

/-- The evaluated interval of a closed expression lies in `[lo, hi)`: `decimalLowerCheck` on the
interval that the evaluator returns, and `false` when it returns none. -/
def lowerCheck (p : Precision) (expr : Verified.Expr (Fin 0)) (lo hi : ℚ) : Bool :=
  match eval p closedEnv expr with
  | some I => I.decimalLowerCheck lo hi
  | none => false

/-- The evaluated interval of a closed expression lies in `(lo, hi]`: `decimalUpperCheck` on the
interval that the evaluator returns, and `false` when it returns none. -/
def upperCheck (p : Precision) (expr : Verified.Expr (Fin 0)) (lo hi : ℚ) : Bool :=
  match eval p closedEnv expr with
  | some I => I.decimalUpperCheck lo hi
  | none => false

/-- The evaluated interval of a closed expression lies in `[lo, hi]`: `decimalEnclosureCheck` on
the interval that the evaluator returns, and `false` when it returns none. -/
def enclosureCheck (p : Precision) (expr : Verified.Expr (Fin 0)) (lo hi : ℚ) : Bool :=
  match eval p closedEnv expr with
  | some I => I.decimalEnclosureCheck lo hi
  | none => false

private theorem closedEnv_sound (ρ : Fin 0 → ℝ) : ∀ i, (closedEnv i).MemReal (ρ i) :=
  fun i ↦ i.elim0

/-- If `lowerCheck p expr lo hi = true` for a closed expression, then `lo ≤ expr.eval ρ < hi` for
the (empty) environment `ρ`: `RationalInterval.of_decimalLowerCheck'` at the evaluated interval,
which contains the value by `eval_sound`. -/
theorem of_lowerCheck {p : Precision} {expr : Verified.Expr (Fin 0)} {lo hi : ℚ}
    (h : lowerCheck p expr lo hi = true) (ρ : Fin 0 → ℝ) :
    (lo : ℝ) ≤ expr.eval ρ ∧ expr.eval ρ < hi := by
  unfold lowerCheck at h
  cases hI : eval p closedEnv expr with
  | none => simp [hI] at h
  | some I =>
      simp only [hI] at h
      exact RationalInterval.of_decimalLowerCheck'
        (eval_sound p closedEnv ρ (closedEnv_sound ρ) expr hI) h

/-- If `upperCheck p expr lo hi = true` for a closed expression, then `lo < expr.eval ρ ≤ hi` for
the (empty) environment `ρ`: `RationalInterval.of_decimalUpperCheck'` at the evaluated
interval. -/
theorem of_upperCheck {p : Precision} {expr : Verified.Expr (Fin 0)} {lo hi : ℚ}
    (h : upperCheck p expr lo hi = true) (ρ : Fin 0 → ℝ) :
    (lo : ℝ) < expr.eval ρ ∧ expr.eval ρ ≤ hi := by
  unfold upperCheck at h
  cases hI : eval p closedEnv expr with
  | none => simp [hI] at h
  | some I =>
      simp only [hI] at h
      exact RationalInterval.of_decimalUpperCheck'
        (eval_sound p closedEnv ρ (closedEnv_sound ρ) expr hI) h

/-- If `enclosureCheck p expr lo hi = true` for a closed expression, then `lo ≤ expr.eval ρ ≤ hi`
for the (empty) environment `ρ`: `RationalInterval.of_decimalEnclosureCheck'` at the evaluated
interval. -/
theorem of_enclosureCheck {p : Precision} {expr : Verified.Expr (Fin 0)} {lo hi : ℚ}
    (h : enclosureCheck p expr lo hi = true) (ρ : Fin 0 → ℝ) :
    (lo : ℝ) ≤ expr.eval ρ ∧ expr.eval ρ ≤ hi := by
  unfold enclosureCheck at h
  cases hI : eval p closedEnv expr with
  | none => simp [hI] at h
  | some I =>
      simp only [hI] at h
      exact RationalInterval.of_decimalEnclosureCheck'
        (eval_sound p closedEnv ρ (closedEnv_sound ρ) expr hI) h

/-- The digits of a positive value: if `lowerCheck` passes for the bounds `m / 10 ^ k` and
`(m + 1) / 10 ^ k`, the value `x` of `expr` satisfies `m / 10 ^ k ≤ x < (m + 1) / 10 ^ k`. -/
theorem of_lowerCheck_decimal {p : Precision} {expr : Verified.Expr (Fin 0)} {m k : ℕ}
    (h : lowerCheck p expr ((m : ℚ) / 10 ^ k) (((m : ℚ) + 1) / 10 ^ k) = true)
    (ρ : Fin 0 → ℝ) :
    (m : ℝ) / 10 ^ k ≤ expr.eval ρ ∧ expr.eval ρ < ((m : ℝ) + 1) / 10 ^ k := by
  simpa using of_lowerCheck h ρ

/-- The digits of a negative value: if `upperCheck` passes for the bounds `-(m + 1) / 10 ^ k` and
`-m / 10 ^ k`, the value `x` of `expr` satisfies `-(m + 1) / 10 ^ k < x ≤ -m / 10 ^ k`. -/
theorem of_upperCheck_decimal {p : Precision} {expr : Verified.Expr (Fin 0)} {m k : ℕ}
    (h : upperCheck p expr (-((m : ℚ) + 1) / 10 ^ k) (-(m : ℚ) / 10 ^ k) = true)
    (ρ : Fin 0 → ℝ) :
    -((m : ℝ) + 1) / 10 ^ k < expr.eval ρ ∧ expr.eval ρ ≤ -(m : ℝ) / 10 ^ k := by
  simpa using of_upperCheck h ρ

/-- The leading digits of a large positive value: if `lowerCheck` passes for the bounds
`m 10 ^ k` and `(m + 1) 10 ^ k`, the value `x` of `expr` satisfies
`m 10 ^ k ≤ x < (m + 1) 10 ^ k`. -/
theorem of_lowerCheck_scaled {p : Precision} {expr : Verified.Expr (Fin 0)} {m k : ℕ}
    (h : lowerCheck p expr ((m : ℚ) * 10 ^ k) (((m : ℚ) + 1) * 10 ^ k) = true)
    (ρ : Fin 0 → ℝ) :
    (m : ℝ) * 10 ^ k ≤ expr.eval ρ ∧ expr.eval ρ < ((m : ℝ) + 1) * 10 ^ k := by
  simpa using of_lowerCheck h ρ

/-- The leading digits of a large negative value: if `upperCheck` passes for the bounds
`-(m + 1) 10 ^ k` and `-m 10 ^ k`, the value `x` of `expr` satisfies
`-(m + 1) 10 ^ k < x ≤ -m 10 ^ k`. -/
theorem of_upperCheck_scaled {p : Precision} {expr : Verified.Expr (Fin 0)} {m k : ℕ}
    (h : upperCheck p expr (-((m : ℚ) + 1) * 10 ^ k) (-(m : ℚ) * 10 ^ k) = true)
    (ρ : Fin 0 → ℝ) :
    -((m : ℝ) + 1) * 10 ^ k < expr.eval ρ ∧ expr.eval ρ ≤ -(m : ℝ) * 10 ^ k := by
  simpa using of_upperCheck h ρ

/-- A decimal enclosure: if `enclosureCheck` passes for the bounds `lo / 10 ^ k` and
`hi / 10 ^ k`, the value `x` of `expr` satisfies `lo / 10 ^ k ≤ x ≤ hi / 10 ^ k`. -/
theorem of_enclosureCheck_decimal {p : Precision} {expr : Verified.Expr (Fin 0)} {lo hi : ℤ}
    {k : ℕ} (h : enclosureCheck p expr ((lo : ℚ) / 10 ^ k) ((hi : ℚ) / 10 ^ k) = true)
    (ρ : Fin 0 → ℝ) :
    (lo : ℝ) / 10 ^ k ≤ expr.eval ρ ∧ expr.eval ρ ≤ (hi : ℝ) / 10 ^ k := by
  simpa using of_enclosureCheck h ρ

end DigitsEval
end CAS.Continuum

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Expr.Syntax
public import FloatLib.Numerics.Enclosure.Expression.CheckProof
public import FloatLib.Numerics.Enclosure.Expression.ExtensionsProof
public import FloatLib.Numerics.Enclosure.Expression.StandardProof

/-!
# Translating symbolic expressions to FloatLib

`Expr.toFloatLib` writes an expression of `CAS.Verified.Expr` as an expression of FloatLib,
`FloatLib.Numerics.Interval.Expr`, which every interval backend of FloatLib evaluates: exact
rationals, the binary grid, or an outward rounding into a floating-point format. It is the only
translation between the two languages. `eval_toFloatLib` says that it keeps the value, with no
condition on the expression, so `containsReal_evalZero?` and `holds_of_checkZero` turn FloatLib's
enclosures and checks of a translated expression into statements about the SymLean expression.

FloatLib numbers its variables. Over a box with coordinates `Fin n` the translation takes
`Fin.val`, so that FloatLib's subdivision splits a coordinate everywhere it occurs. Labels of an
arbitrary type need not have decidable equality, so `numberOccurrences` gives each occurrence of
a variable its own number, in the order of `occurrences`, and the input box repeats the interval
of the variable at each of its occurrences (`containsReal_occurrences`). Without subdivision the
two numberings give the same enclosure.

`lowerDivisions` writes a quotient `a / b` whose denominator has a known bound `δ ≤ |b|` as
`a * w`, where `w` is a fresh variable for `b⁻¹` with the interval `[-1/δ, 1/δ]`. Such a bound
usually holds only on a chart, the domain of a certificate, and so it cannot be a registered call
of FloatLib: a call has to enclose its function at every member of its argument interval. As a
fresh input, the bound enters through the proof that each input lies in its interval
(`containsReal_loweredIntervals`).

## Main definitions

* `Expr.toFloatLib`: the translation, with the variable numbering `vars`.
* `Expr.occurrences`, `Expr.numberOccurrences`, `Expr.occurrenceValues`: the variables of an
  expression, one for each occurrence, the expression with its occurrences numbered, and the real
  inputs of the numbered expression.
* `Expr.lowerDivisions`, `Expr.loweredValues`, `Expr.loweredIntervals`: the lowering of the
  quotients with a known denominator bound, and the values and intervals of its variables.

## Main results

* `Expr.eval_toFloatLib`: the translation keeps the value.
* `Expr.containsReal_evalZero?`, `Expr.holds_of_checkZero`: FloatLib's enclosure of a translated
  expression, and its Boolean check on a rational box, for every sound backend with FloatLib's
  standard calls.
* `Expr.eval_numberOccurrences`, `Expr.containsReal_occurrences`,
  `Expr.containsReal_evalZero?_numberOccurrences`: numbering keeps the value, the occurrence
  inputs of a point lie in the occurrence box, and FloatLib's enclosure of the numbered expression
  contains the value of the expression.
* `Expr.eval_lowerDivisions`, `Expr.containsReal_loweredIntervals`: lowering keeps the value, and
  each input of the lowered expression lies in its interval where the denominator bounds hold.

## Implementation notes

FloatLib's constants are rationals and its powers have natural exponents. So `π`, the real power
`a ^ b` and `e` are the calls `0`, `1` and `2` of FloatLib's standard calls,
`Backend.Standard.extensions`, whose real functions are `Backend.Standard.functions`. The
enclosures of `π` and `e` follow the configured precision, while `exp 1` would be enclosed at the
degree of the exponential. A rational literal `num / den` is the constant `Kernel.Q.mk num den`,
the fraction in lowest terms that FloatLib computes quickly in the kernel, which is `0` when
`den = 0`, like Lean's division.

Mathlib's square root, inverse sine and inverse cosine are total, while FloatLib's default
enclosures (`Backend.elementaryBounds?`) need an argument interval with a nonnegative lower end
for the square root, and one inside `[-1, 1]` for the other two. So the argument of `sqrt` goes
through `max 0`, and those of `asin` and `acos` through `max (-1) (min 1 _)`. Both forms keep the
value (`Real.arcsin_projIcc` for the second), and they keep an enclosure when rounding pushes an
end of an argument interval just past the domain. No clamp keeps the value of the logarithm or of
the real power, so they go to FloatLib as they are. Its real power needs a base interval with a
positive lower end, and so does its logarithm in the default enclosures.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, 2026, <https://github.com/lean-dojo/FloatLib>. We use its expression
  language, its interval backends, its standard calls and their soundness theorems.
-/

@[expose] public section

open FloatLib.Numerics FloatLib.Numerics.Interval

namespace CAS.Verified.Expr

variable {ι : Type*}

/-! ## The translation -/

/--
The FloatLib expression with the value of `expr`, where variable `i` is the input at index
`vars i` (`eval_toFloatLib`). A box with coordinates `Fin n` takes `vars := Fin.val`, and labels
of any other type are numbered by occurrence first (`numberOccurrences`).

Literals become rational constants, and `π`, `a ^ b` and `e` are the calls `0`, `1` and `2` of
FloatLib's standard calls `Backend.Standard.extensions`. The argument of `sqrt` goes through
`max 0`, and those of `asin` and `acos` through `max (-1) (min 1 _)`, which keeps the value of
Mathlib's total functions and keeps the argument interval inside the domain of FloatLib's
enclosure. The other operations are FloatLib's operations of the same name. The translation never
fuses a product and a sum into FloatLib's ternary `fma`.
-/
def toFloatLib (vars : ι → Nat) : Expr ι → Interval.Expr
  | .nat n => .const n
  | .int n => .const n
  | .rat num den => .const (Kernel.Q.mk num den)
  | .pi => .call 0 []
  | .e => .call 2 []
  | .var i => .var (vars i)
  | .add a b => .binary .add (a.toFloatLib vars) (b.toFloatLib vars)
  | .mul a b => .binary .mul (a.toFloatLib vars) (b.toFloatLib vars)
  | .sub a b => .binary .sub (a.toFloatLib vars) (b.toFloatLib vars)
  | .div a b => .binary .div (a.toFloatLib vars) (b.toFloatLib vars)
  | .neg a => .unary .neg (a.toFloatLib vars)
  | .pow a n => .unary (.pow n) (a.toFloatLib vars)
  | .sin a => .unary .sin (a.toFloatLib vars)
  | .cos a => .unary .cos (a.toFloatLib vars)
  | .atan a => .unary .atan (a.toFloatLib vars)
  | .asin a =>
      .unary .asin (.binary .max (.const (-1)) (.binary .min (.const 1) (a.toFloatLib vars)))
  | .acos a =>
      .unary .acos (.binary .max (.const (-1)) (.binary .min (.const 1) (a.toFloatLib vars)))
  | .exp a => .unary .exp (a.toFloatLib vars)
  | .log a => .unary .log (a.toFloatLib vars)
  | .sqrt a => .unary .sqrt (.binary .max (.const 0) (a.toFloatLib vars))
  | .rpow a b => .call 1 [a.toFloatLib vars, b.toFloatLib vars]

private theorem arcsin_clamp (x : ℝ) : Real.arcsin (max (-1) (min 1 x)) = Real.arcsin x := by
  simpa [Set.coe_projIcc] using Real.arcsin_projIcc x

private theorem arccos_clamp (x : ℝ) : Real.arccos (max (-1) (min 1 x)) = Real.arccos x := by
  simp only [Real.arccos_eq_pi_div_two_sub_arcsin, arcsin_clamp]

private theorem sqrt_clamp (x : ℝ) : Real.sqrt (max 0 x) = Real.sqrt x := by
  rcases le_total x 0 with h | h
  · rw [max_eq_left h, Real.sqrt_zero, Real.sqrt_eq_zero'.mpr h]
  · rw [max_eq_right h]

/--
The translation keeps the value: FloatLib's value of `expr.toFloatLib vars`, with the real
functions `Backend.Standard.functions` for its calls, is SymLean's value of `expr` at `ρ`, for
every assignment `values` that gives the index `vars i` the value `ρ i`. There is no other
hypothesis.

Rewriting the conclusion of FloatLib's `Interval.Expr.containsReal_evalZero?` with this equality
gives an enclosure of the SymLean expression.
-/
theorem eval_toFloatLib (expr : Expr ι) (vars : ι → Nat) (ρ : ι → ℝ) (values : Nat → ℝ)
    (hvars : ∀ i, values (vars i) = ρ i) :
    (expr.toFloatLib vars).eval values (extensionValues Backend.Standard.functions) =
      expr.eval ρ := by
  induction expr with
  | nat n => simp [toFloatLib, Interval.Expr.eval]
  | int n => simp [toFloatLib, Interval.Expr.eval]
  | rat num den => simp [toFloatLib, Interval.Expr.eval, Rat.mkRat_eq_div]
  | pi | e => rfl
  | var i => simpa [toFloatLib, Interval.Expr.eval] using hvars i
  | add a b iha ihb | mul a b iha ihb | sub a b iha ihb | div a b iha ihb =>
    simp [toFloatLib, Interval.Expr.eval, BinaryOp.eval, iha, ihb]
  | neg a ih | pow a n ih | sin a ih | cos a ih | atan a ih | exp a ih | log a ih =>
    simp [toFloatLib, Interval.Expr.eval, UnaryOp.eval, ih]
  | asin a ih => simp [toFloatLib, Interval.Expr.eval, UnaryOp.eval, BinaryOp.eval, ih,
      arcsin_clamp]
  | acos a ih => simp [toFloatLib, Interval.Expr.eval, UnaryOp.eval, BinaryOp.eval, ih,
      arccos_clamp]
  | sqrt a ih => simp [toFloatLib, Interval.Expr.eval, UnaryOp.eval, BinaryOp.eval, ih,
      sqrt_clamp]
  | rpow a b iha ihb =>
    simp only [toFloatLib, Interval.Expr.eval, Interval.Expr.evalArgs, iha, ihb]
    rfl

variable {α : Type*} {B : Backend α} {functions : Nat → List ℝ → ℝ} {config : Backend.Config}
  {vars : ι → Nat} {ρ : ι → ℝ} {values : Nat → ℝ}

/--
A successful FloatLib evaluation with the zero rule of `expr.toFloatLib vars`, by a sound backend
`B` with FloatLib's standard calls added, contains SymLean's value of `expr` at `ρ`. The interval
environment `env` must contain `values k` at every index `k` that it fills, and `values` must
give the index `vars i` the value `ρ i`. This is FloatLib's `Interval.Expr.containsReal_evalZero?`
after `eval_toFloatLib`.
-/
theorem containsReal_evalZero? (hB : B.Sound functions) (hvars : ∀ i, values (vars i) = ρ i)
    {env : Nat → Option (Interval α)}
    (henv : ∀ k I, env k = some I → I.ContainsReal B.decode (values k))
    (expr : Expr ι) {I : Interval α}
    (h : (expr.toFloatLib vars).evalZero? (B.withExtensions config Backend.Standard.extensions)
      env = some I) :
    I.ContainsReal B.decode (expr.eval ρ) := by
  rw [← eval_toFloatLib expr vars ρ values hvars]
  exact (expr.toFloatLib vars).containsReal_evalZero?
    (Backend.withExtensions_sound hB config Backend.Standard.extensions_sound) henv h

/--
A passing FloatLib check with the zero rule of `expr.toFloatLib vars` on the rational box `box`,
by a sound backend `B` with FloatLib's standard calls added, proves `relation` (`expr ≤ 0` or
`expr < 0`) for SymLean's value of `expr` at `ρ`, for every assignment `values` in the box that
gives the index `vars i` the value `ρ i`. This is FloatLib's `Interval.Expr.checkZero_sound`
after `eval_toFloatLib`.
-/
theorem holds_of_checkZero (hB : B.Sound functions) (hvars : ∀ i, values (vars i) = ρ i)
    {relation : Relation} {box : Box} {depth : Nat} (expr : Expr ι)
    (h : (expr.toFloatLib vars).checkZero (B.withExtensions config Backend.Standard.extensions)
      relation box depth = true)
    (hbox : box.ContainsReal values) : relation.Holds (expr.eval ρ) := by
  rw [← eval_toFloatLib expr vars ρ values hvars]
  exact (expr.toFloatLib vars).checkZero_sound
    (Backend.withExtensions_sound hB config Backend.Standard.extensions_sound) h hbox

/-! ## Numbering by occurrence -/

/-- The variables of `expr`, one entry for each occurrence, in the order in which
`numberOccurrences` numbers them: from left to right, the left operand before the right one. -/
def occurrences : Expr ι → List ι
  | .nat _ | .int _ | .rat _ _ | .pi | .e => []
  | .var i => [i]
  | .add a b | .mul a b | .sub a b | .div a b | .rpow a b => a.occurrences ++ b.occurrences
  | .neg a | .pow a _ | .sin a | .cos a | .atan a | .asin a | .acos a | .exp a | .log a |
      .sqrt a => a.occurrences

/--
`expr` with its variable occurrences numbered `start`, `start + 1`, … in the order of
`occurrences`. Each occurrence gets its own number, so no equality of labels is decided, and
`(expr.numberOccurrences 0).toFloatLib id` is a FloatLib expression for labels of any type.
-/
def numberOccurrences (start : Nat) : Expr ι → Expr Nat
  | .nat n => .nat n
  | .int n => .int n
  | .rat num den => .rat num den
  | .pi => .pi
  | .e => .e
  | .var _ => .var start
  | .add a b => .add (a.numberOccurrences start)
      (b.numberOccurrences (start + a.occurrences.length))
  | .mul a b => .mul (a.numberOccurrences start)
      (b.numberOccurrences (start + a.occurrences.length))
  | .sub a b => .sub (a.numberOccurrences start)
      (b.numberOccurrences (start + a.occurrences.length))
  | .div a b => .div (a.numberOccurrences start)
      (b.numberOccurrences (start + a.occurrences.length))
  | .neg a => .neg (a.numberOccurrences start)
  | .pow a n => .pow (a.numberOccurrences start) n
  | .sin a => .sin (a.numberOccurrences start)
  | .cos a => .cos (a.numberOccurrences start)
  | .atan a => .atan (a.numberOccurrences start)
  | .asin a => .asin (a.numberOccurrences start)
  | .acos a => .acos (a.numberOccurrences start)
  | .exp a => .exp (a.numberOccurrences start)
  | .log a => .log (a.numberOccurrences start)
  | .sqrt a => .sqrt (a.numberOccurrences start)
  | .rpow a b => .rpow (a.numberOccurrences start)
      (b.numberOccurrences (start + a.occurrences.length))

/-- The real inputs of `expr.numberOccurrences 0` at the point `ρ`: the index `k` holds the value
of the variable of the `k`-th occurrence, and an index past the last occurrence holds `0`. -/
noncomputable def occurrenceValues (ρ : ι → ℝ) (expr : Expr ι) (k : Nat) : ℝ :=
  (expr.occurrences[k]?.map ρ).getD 0

/-- Numbering keeps the value: `expr.numberOccurrences start` has the value of `expr` at `ρ` for
every assignment `values` that gives the number `start + k` the value of the variable of the
`k`-th occurrence. -/
theorem eval_numberOccurrences (expr : Expr ι) {start : Nat} {values : Nat → ℝ}
    (h : ∀ k i, expr.occurrences[k]? = some i → values (start + k) = ρ i) :
    (expr.numberOccurrences start).eval values = expr.eval ρ := by
  induction expr generalizing start with
  | nat | int | rat | pi | e => rfl
  | var i => simpa [numberOccurrences, occurrences] using h 0 i rfl
  | add a b iha ihb | mul a b iha ihb | sub a b iha ihb | div a b iha ihb
  | rpow a b iha ihb =>
    have hb : ∀ k i, b.occurrences[k]? = some i →
        values (start + a.occurrences.length + k) = ρ i := fun k i hk ↦ by
      simpa [Nat.add_assoc, occurrences, List.getElem?_append_right, hk] using
        h (a.occurrences.length + k) i
    have ha : ∀ k i, a.occurrences[k]? = some i → values (start + k) = ρ i := fun k i hk ↦
      h k i (by simp [occurrences, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hk).1,
        hk])
    simp [numberOccurrences, iha ha, ihb hb]
  | neg a ih | pow a n ih | sin a ih | cos a ih | atan a ih | asin a ih | acos a ih | exp a ih
  | log a ih | sqrt a ih =>
    simp [numberOccurrences, ih h]

/-- The occurrence inputs `occurrenceValues ρ expr` lie in the box `expr.occurrences.map
intervals`, which repeats the interval of a variable at each of its occurrences, when the
interval of each variable of `expr` contains its value at `ρ`. -/
theorem containsReal_occurrences {intervals : ι → Interval ℚ} {expr : Expr ι}
    (h : ∀ i ∈ expr.occurrences, (intervals i).ContainsReal some (ρ i)) :
    Box.ContainsReal (expr.occurrences.map intervals) (occurrenceValues ρ expr) := by
  intro k I hI
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 (List.getElem?_map ▸ hI)
  simpa [occurrenceValues, hi] using h i (List.mem_of_getElem? hi)

/--
A successful FloatLib evaluation with the zero rule of the numbered expression
`(expr.numberOccurrences 0).toFloatLib id`, by a sound backend `B` with FloatLib's standard calls
added, contains SymLean's value of `expr` at `ρ`. The interval environment `env` must contain the
occurrence input `occurrenceValues ρ expr k` at every index `k` that it fills, as an environment
read from the box of `containsReal_occurrences` does. This is `containsReal_evalZero?` after
`eval_numberOccurrences`.
-/
theorem containsReal_evalZero?_numberOccurrences (hB : B.Sound functions) {expr : Expr ι}
    {env : Nat → Option (Interval α)}
    (henv : ∀ k I, env k = some I → I.ContainsReal B.decode (occurrenceValues ρ expr k))
    {I : Interval α}
    (h : ((expr.numberOccurrences 0).toFloatLib id).evalZero?
      (B.withExtensions config Backend.Standard.extensions) env = some I) :
    I.ContainsReal B.decode (expr.eval ρ) := by
  rw [← expr.eval_numberOccurrences (start := 0) (values := occurrenceValues ρ expr)
    fun k i hk ↦ by simp [occurrenceValues, hk]]
  exact containsReal_evalZero? hB (ρ := occurrenceValues ρ expr) (fun _ ↦ rfl) henv _ h

/-! ## Quotients with a known denominator bound -/

/--
`expr` with each quotient `a / b` whose denominator has a bound `lookup b = some δ` written as
the product `a * w`, where `w` is a fresh variable with the label `.inr (b, δ)` and the value
`b⁻¹`. The variables of `expr` keep their labels, as `.inl i`, and the other operations stay.

Where `0 < δ ≤ |b|`, the value of `w` lies in `[-1/δ, 1/δ]` (`containsReal_loweredIntervals`), so
FloatLib encloses the product even when the enclosure of `b` contains zero. Only the bound of `b`
is read, never its value: `b` is not evaluated.
-/
def lowerDivisions (lookup : Expr ι → Option ℚ) : Expr ι → Expr (ι ⊕ Expr ι × ℚ)
  | .nat n => .nat n
  | .int n => .int n
  | .rat num den => .rat num den
  | .pi => .pi
  | .e => .e
  | .var i => .var (.inl i)
  | .add a b => .add (a.lowerDivisions lookup) (b.lowerDivisions lookup)
  | .mul a b => .mul (a.lowerDivisions lookup) (b.lowerDivisions lookup)
  | .sub a b => .sub (a.lowerDivisions lookup) (b.lowerDivisions lookup)
  | .div a b =>
      match lookup b with
      | some δ => .mul (a.lowerDivisions lookup) (.var (.inr (b, δ)))
      | none => .div (a.lowerDivisions lookup) (b.lowerDivisions lookup)
  | .neg a => .neg (a.lowerDivisions lookup)
  | .pow a n => .pow (a.lowerDivisions lookup) n
  | .sin a => .sin (a.lowerDivisions lookup)
  | .cos a => .cos (a.lowerDivisions lookup)
  | .atan a => .atan (a.lowerDivisions lookup)
  | .asin a => .asin (a.lowerDivisions lookup)
  | .acos a => .acos (a.lowerDivisions lookup)
  | .exp a => .exp (a.lowerDivisions lookup)
  | .log a => .log (a.lowerDivisions lookup)
  | .sqrt a => .sqrt (a.lowerDivisions lookup)
  | .rpow a b => .rpow (a.lowerDivisions lookup) (b.lowerDivisions lookup)

/-- The values of the variables of `expr.lowerDivisions lookup` at the point `ρ`: `ρ i` for a
variable `i` of `expr`, and `(b.eval ρ)⁻¹` for the fresh variable of a denominator `b`. -/
noncomputable def loweredValues (ρ : ι → ℝ) : ι ⊕ Expr ι × ℚ → ℝ :=
  Sum.elim ρ fun d ↦ (d.1.eval ρ)⁻¹

/-- The intervals of the variables of `expr.lowerDivisions lookup`: `intervals i` for a variable
`i` of `expr`, and `[-1/δ, 1/δ]` for the fresh variable of a denominator with the bound `δ`. -/
def loweredIntervals (intervals : ι → Interval ℚ) : ι ⊕ Expr ι × ℚ → Interval ℚ :=
  Sum.elim intervals fun d ↦ ⟨Kernel.Q.neg (Kernel.Q.inv d.2), Kernel.Q.inv d.2⟩

/-- Lowering keeps the value, whatever the bounds: `a / b = a * b⁻¹` in `ℝ`, at `b = 0` too. -/
@[simp] theorem eval_lowerDivisions (lookup : Expr ι → Option ℚ) (ρ : ι → ℝ) (expr : Expr ι) :
    (expr.lowerDivisions lookup).eval (loweredValues ρ) = expr.eval ρ := by
  induction expr with
  | var i => rfl
  | div a b iha ihb =>
    cases h : lookup b with
    | some δ =>
      simp only [lowerDivisions, h, eval, iha, div_eq_mul_inv]
      rfl
    | none => simp only [lowerDivisions, h, eval, iha, ihb]
  | _ => simp_all [lowerDivisions]

/-- A property holds at every variable of `expr.lowerDivisions lookup` when it holds at each
variable `.inl i` of `expr` and at each fresh variable `.inr (b, δ)` with `lookup b = some δ`. -/
theorem forall_mem_occurrences_lowerDivisions {lookup : Expr ι → Option ℚ} {expr : Expr ι}
    {p : ι ⊕ Expr ι × ℚ → Prop} (hvars : ∀ i ∈ expr.occurrences, p (.inl i))
    (hfresh : ∀ b δ, lookup b = some δ → p (.inr (b, δ))) :
    ∀ l ∈ (expr.lowerDivisions lookup).occurrences, p l := by
  induction expr with
  | nat | int | rat | pi | e => simp [lowerDivisions, occurrences]
  | var i => simpa [lowerDivisions, occurrences] using hvars
  | add a b iha ihb | mul a b iha ihb | sub a b iha ihb | rpow a b iha ihb =>
    simp only [lowerDivisions, occurrences, List.forall_mem_append] at hvars ⊢
    exact ⟨iha hvars.1, ihb hvars.2⟩
  | div a b iha ihb =>
    simp only [occurrences, List.forall_mem_append] at hvars
    cases h : lookup b with
    | some δ =>
      simp only [lowerDivisions, h, occurrences, List.forall_mem_append,
        List.forall_mem_singleton]
      exact ⟨iha hvars.1, hfresh b δ h⟩
    | none =>
      simp only [lowerDivisions, h, occurrences, List.forall_mem_append]
      exact ⟨iha hvars.1, ihb hvars.2⟩
  | neg a ih | pow a n ih | sin a ih | cos a ih | atan a ih | asin a ih | acos a ih | exp a ih
  | log a ih | sqrt a ih => exact ih hvars

/--
Each variable of `expr.lowerDivisions lookup` has its value at `ρ` in its interval: a variable of
`expr` when its interval contains its value, and the fresh variable of a denominator `b` with
`lookup b = some δ` when `0 < δ ≤ |b|` at `ρ`. With `containsReal_occurrences`, the occurrence
inputs of the lowered expression then lie in its occurrence box.
-/
theorem containsReal_loweredIntervals {intervals : ι → Interval ℚ} {lookup : Expr ι → Option ℚ}
    {expr : Expr ι} (hvars : ∀ i ∈ expr.occurrences, (intervals i).ContainsReal some (ρ i))
    (hlookup : ∀ b δ, lookup b = some δ → 0 < δ ∧ (δ : ℝ) ≤ |b.eval ρ|) :
    ∀ l ∈ (expr.lowerDivisions lookup).occurrences,
      (loweredIntervals intervals l).ContainsReal some (loweredValues ρ l) :=
  forall_mem_occurrences_lowerDivisions hvars fun b δ hb ↦ by
    obtain ⟨hδ, hle⟩ := hlookup b δ hb
    have hinv : |(b.eval ρ)⁻¹| ≤ (δ : ℝ)⁻¹ := by
      rw [abs_inv]
      exact inv_anti₀ (by exact_mod_cast hδ) hle
    simpa [loweredIntervals, loweredValues, Kernel.Q.neg_eq, Kernel.Q.inv_eq] using
      abs_le.1 hinv

end CAS.Verified.Expr

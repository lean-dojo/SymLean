/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.CEGA.Elaboration
public meta import CAS.CEGA.Elaboration

/-!
# CEGA tactic syntax

The syntax of the `cega` tactic family. The arguments of `cega` form the syntax category
`cegaArgs`, which `cega?` of `CAS.Reporting` parses too. The forms are

* `cega`, which projects a checked carrier, decides a closed statement about floats as
  `float_decide` does, proves a bound on an interval integral by a checked batch quadrature,
  infers a rational box from local hypotheses or from the domain of a certificate goal, or runs
  FloatLib's `interval`, and `cega using t`, which uses the supplied carrier `t`;
  `cega (prec := n) (depth := n) (panels := n)` sets the precision and subdivision depth of the
  inferred box query and of `interval`, and the panel count of an integral bound;
* `cega [fast]`, which tries `float_decide`, then closed finite and polynomial certificates
  according to the `cega.nativeCertificates` checking profile;
* `cega [use_floats]`, which computes the enclosures with IEEE floats instead of exact rationals
  (see below);
* `cega (cfg) [enclose x in [a, b], ...] e`, the explicit box query, which proves the
  projection the goal needs: an enclosure, an upper bound, an absolute bound or a midpoint
  approximation.

In the explicit query form each binding `x in [a, b]` (syntax category
`cegaIntervalBinding`) gives a coordinate and its closed interval with rational endpoints.
The optional configuration group sets the precision policy, as in `(prec := 40)`, and
`(depth := n)` subdivides the box. The goal may be a certificate proposition (`EnclosedOn`,
`BoundOn`, `ApproxOn`) on the box or an ordinary inequality in the box variables, and the proof
is built from a kernel-checked certificate theorem.

## The arithmetic

By default `cega` computes with exact integers and rationals. The flag `use_floats` switches the
enclosures of the box query to intervals whose two ends are IEEE floats, each lower end rounded
toward `-∞` and each upper end toward `+∞`, with every float operation evaluated by the kernel
through FloatLib:

* `cega [use_floats]` and `cega [use_floats := true]` compute in binary64, or in the format of
  the option `cega.arithmetic` where it names one; `cega [use_floats := false]` is the default,
  exact arithmetic.
* `cega [use_floats := true] (arith := binary32)` chooses the format. The value of `arith` is
  any IEEE binary format of FloatLib, a term of type `FloatFormat` read with FloatLib's format
  names in scope: `binary16`, `binary32`, `binary64`, `binary128`, `FloatFormat.ieee 15 112` for
  15 exponent bits and 112 fraction bits, or a definition of your own. It may also be a string,
  as in `(arith := "binary(p := 113, emax := 16383)")`, which names a format by its precision
  and its largest exponent as IEEE 754 does. `(arith := F)` alone turns floats on, so
  `cega (arith := binary128)` needs no flag.
* `set_option cega.arithmetic "binary64"` sets the arithmetic of the `cega` calls of a section,
  with the same text; `"exact"` is its default. A call overrides it with the flag or the item,
  and an explicit query overrides it with `(arith := "exact")`.
* A project sets the option for a whole build, with no change to a Lean file: one line of its
  lakefile passes `weak.cega.arithmetic` to every module, `weak.cega.arithmetic = "binary64"`
  under `[leanOptions]` of `lakefile.toml`, or
  ``leanOptions := #[⟨`weak.cega.arithmetic, "binary64"⟩]`` in `lakefile.lean`, where the value
  can come from the command line (`lake build -R -Karithmetic=binary64` with
  `(get_config? arithmetic).getD "exact"`). `tests/floats` builds such a package both ways.
* The flag sits in the bracket group with the other flags, in any order, as in
  `cega [fast, use_floats]`, and the configuration items follow the group, as in
  `cega [use_floats] (arith := binary128) (depth := 6)`. `cega (arith := F) [enclose x in [a, b]] e`
  is the explicit query in the format `F`.

With floats on, `(depth := n)` sets the depth of the subdivision, and the other
precision items, which configure the series of the exact evaluator, are not used: the format is
the precision. A float query that does not prove the goal fails with the format's name and the
reason (an overflow, a divisor that contains zero, an enclosure that is too wide), and proposes
a wider format or exact arithmetic; `cega` never computes with rationals in its place. The
quadrature of an integral, FloatLib's `interval` and `dyadic_interval` compute with exact
numbers, so `cega` does not run them when floats are on, while `float_decide` evaluates the floats
that a statement names and runs in either arithmetic. `cega?` prints the arithmetic that a proof
used.

## Implementation notes

We keep the grammar apart from the elaborators of `CAS.CEGA` because `CAS.Tactic.BoxInequality`,
which `CAS.CEGA` imports, builds replay suggestions from it: the bare call or the explicit query
that reproduces a proof (`BoxInequality.bareSyntax`, `BoxInequality.querySyntax`).
`CAS.Numerics.Tactic` adds `cega [batch := n]` and `cega [fast, batch := n]` to `cegaArgs`. Every
form ends in a theorem that the kernel checks; only the `fast` forms with
`cega.nativeCertificates = true` also trust Lean's compiler and runtime, through `nativeEqTrue`.

The bracket group of a call with `use_floats` is one rule, `cegaFloats`: the flag, with any
flags of the category `cegaFlag` before and after it. The category has `fast` here, and
`CAS.Numerics.Tactic` adds `batch := n`. The rule matches only a group that has `use_floats`, so
`cega [fast]`, `cega [batch := n]` and `cega [fast, batch := n]` use their own syntax rules.
-/

public meta section

namespace CAS.CEGA

open Lean Elab Tactic Parser.Tactic
open CAS.CEGA.Elaboration

/-- The arguments of `cega`, shared with `cega?`. -/
declare_syntax_cat cegaArgs

/-- `cega` proves real inequalities on boxes, closed numerical bounds, bounds on interval
integrals and closed statements about floats from certificates that the kernel checks.

## Theorem
`cega` closes goals of these shapes, with closed bounds `a`, `b` and `c`:

- `f x ≤ c`, `f x < c`, `c ≤ f x`, `c < f x`, `|f x| ≤ c` and `|f x| < c`;
- `a ≤ f x ∧ f x ≤ b`, also with `<`, and `f x ∈ Set.Icc a b`, also with `Set.Ioo`, `Set.Ico`
  and `Set.Ioc`;
- `f x ≤ g x`, and conjunctions of these goals;
- bounds on one interval integral, such as `(∫ x in a..b, f x) ≤ c` and
  `|(∫ x in a..b, f x) - c| ≤ ε`, with rational limits;
- the certificate propositions `EnclosedOn`, `BoundOn`, `ApproxOn` and `ResidualBound` on a box;
- the real and nonnegative real inequalities that FloatLib's `interval` proves, with finite sums,
  norms, dot and matrix products, and the bounds over a whole domain that it reads:
  `∀ u : ℝ, …` for a trigonometric polynomial, `∀ x ∈ Set.Icc lo hi, …` and
  `∀ z : ℂ, ‖z‖ = 1 → …`;
- closed decidable statements about floats, such as `(1.5 : Binary64) + 2.25 = 3.75`, decided in
  the kernel as `float_decide` decides them.

On a box, every real variable is bounded by hypotheses `a ≤ x` and `x ≤ b`, `x ∈ Set.Icc a b` or
`|x| ≤ r` with rational literals; a goal without variables needs none.

## Conditions and limits
The routes run in this order, each only on goals of its shape: a checked carrier of the goal,
`float_decide`, the quadrature of an integral, a certificate goal, the box route, FloatLib's
`interval`, `dyadic_interval` on a closed goal, and a kernel certificate for a closed decidable
proposition that is not about floats. The box route first tries FloatLib's check, which refutes
the negation of the stated bounds on pieces of the box that `cega` chooses, by FloatLib's interval
evaluation checked in the kernel. When that falls short, it encloses the expressions of the goal
on the box of the hypotheses and compares the enclosure with the bound by exact rational arithmetic;
when the first enclosure is too weak, it subdivides the box to depth 2. An integral bound uses
Simpson panels when the domain checker certifies the first four derivatives of the integrand on
`[a, b]`, and range panels, which need only continuity, otherwise or when the Simpson panels fall
short; the panel count doubles from 1 up to `cega.maxIntegrationPanels`. `interval` reads the
bounds in the hypotheses itself, with FloatLib's defaults unless `(prec := n)`, `(digits := d)` or
`(depth := n)` sets them, and `dyadic_interval` runs at 32 bits unless `(prec := n)` or
`(digits := d)` sets them. The functions of the box route are those of the grammar of
`#cas [N d]`, written as Mathlib terms such as `Real.sin x` and `Real.sqrt x`, and a box has at
most 8 variables (`cega.maxDimension`). A false bound, or a true one that the enclosures do not
reach, is refused with the next call to try; for an integral the message gives the interval that
the panel search proposes.

## Options
- `[use_floats]` computes the enclosures of the box route with IEEE floats of the format
  binary64, rounded outward and checked in the kernel, instead of exact rationals;
  `[use_floats := false]` is the default. `(arith := F)` chooses the format `F`, an IEEE binary
  format of FloatLib such as `binary32` or `binary128`, and `set_option cega.arithmetic "binary64"`
  sets the arithmetic of a section.
- `(prec := n)`, `(expOrder := n)`, `(logTerms := n)` and `(sqrtDigits := n)` set the precision
  of the box query as in `#cas [enclose]`; `(prec := n)` also sets the endpoint bits of
  `interval` and the bits of a closed goal, and `(digits := d)` gives both about `3.3 d + 8` bits.
- `(depth := n)` sets the depth of the subdivision tried after the first query, default 2, and
  the subdivision depth of `interval`, which is otherwise FloatLib's default.
- `(panels := n)` fixes the panel count of an integral bound; `(digits := d)` fixes its working
  precision.
- `set_option cega.maxIntegrationPanels n` caps the doubling of the panels, default 256.
- `set_option cega.nativeCertificates true` lets `cega [fast]` check finite certificates with
  compiled code, which also trusts Lean's compiler; the default `false` keeps every check in the
  kernel.

## Examples
```lean
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x ≤ 0.85 := by
  cega
```
```lean
example : Real.exp 1 ≤ 2.72 := by
  cega
```
```lean
example : (∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) ≤ 3 / 4 := by
  cega
```
```lean
example (x : Fin 3 → ℝ) (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) : ∑ i, x i ^ 2 ≤ 3 := by
  cega
```

## In a proof
```lean
theorem cega_sin_lt_one (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x < 1 := by
  have h : Real.sin x ≤ 17 / 20 := by cega
  linarith
```

## See also
Mathematica `Interval` and `NIntegrate`, SymPy `AccumBounds`. The tactics `cega?` and `cas`,
which tries `cega` on ordinary inequalities, and the modes `enclose`, `nintegrate` and `N`.

## Possible issues
```lean
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x ≤ 0.8 := by
  cega
```
```output
cega box route: comparison with the stated bound: the certified value does not give the stated
bound.
```
The bound is false, since `Real.sin 1 > 0.84`. For a true bound that the enclosure misses, the
message proposes `cega (depth := 4)` or `cega (prec := 24)`.
```lean
example (x : ℝ) : x * (1 - x) ≤ 1 / 4 := by
  cega
```
```output
cega box route: no rational bounds on `x` in the hypotheses; the route needs hypotheses `a ≤ x` and
`x ≤ b`, `x ∈ Set.Icc a b`, or `|x| ≤ r` with rational literal endpoints
```
Add bounds on `x` as hypotheses. A bound for every `x`, as here, follows from
`nlinarith [sq_nonneg (2 * x - 1)]`.
-/
syntax (name := tacticCega) "cega" (cegaArgs)? : tactic

/-- The argument of `cega using carrier`. -/
syntax (name := cegaUsing) " using " term : cegaArgs

/-- The argument of `cega [fast]`. -/
syntax (name := cegaFast) " [" &"fast" "]" : cegaArgs

/--
`cega [fast]`

Try `float_decide` on a closed statement about floats, checked in the kernel, then closed finite
and polynomial certificates under the `cega.nativeCertificates` checking profile, then the kernel
routes of bare `cega`. A native certificate also trusts Lean's compiler and runtime; with the
default profile, `cega.nativeCertificates = false`, it is bare `cega`.
-/
tactic_extension tacticCega

/-- A flag of the bracket group of a `cega` call with `use_floats`, as `fast` in
`cega [fast, use_floats]`. `CAS.Numerics.Tactic` adds the flag `batch := n`. -/
declare_syntax_cat cegaFlag (behavior := both)

/-- The flag `fast`. -/
syntax (name := cegaFlagFast) &"fast" : cegaFlag

/-- The flag `use_floats`, which `use_floats := true` also writes, and `use_floats := false`. -/
syntax cegaUseFloats := &"use_floats" (" := " (&"true" <|> &"false"))?

/-- The arguments of `cega [use_floats]`: a bracket group that has the flag `use_floats`, with
any other flags before and after it, and then configuration items. -/
syntax (name := cegaFloats)
  " [" (cegaFlag ", ")* cegaUseFloats (", " cegaFlag)* "]"
    (colGt Lean.Parser.Term.configItem)* : cegaArgs

/--
`cega [use_floats]`

Bare `cega` with the enclosures of its box route computed in IEEE floating-point arithmetic:
`cega [use_floats]` and `cega [use_floats := true]` in binary64, or in the format of the option
`cega.arithmetic` where it names one, `cega [use_floats] (arith := F)` in the IEEE binary format
`F` of FloatLib, and `cega [use_floats := false]` in exact arithmetic, the default. Every lower
end is rounded toward `-∞` and every upper end toward `+∞`, the kernel evaluates the float
operations, and the theorem is about real numbers. The items `(depth := n)` and `(arith := F)`
follow the bracket group, and `fast` may share it. A float computation that does not prove the
goal fails, with the format and the reason.
-/
tactic_extension tacticCega

/-- The other flags of the bracket group of a `cega [… use_floats …]` call, whose arguments
`arguments` have the kind `cegaFloats`, in the order written. -/
partial def otherFlags (arguments : Syntax) : Array Syntax :=
  collect arguments[1] ++ collect arguments[3]
where
  /-- The flag nodes under a repetition: everything but the commas and the grouping nodes. -/
  collect : Syntax → Array Syntax
    | stx@(.node _ kind children) =>
        if kind == nullKind ∨ kind == groupKind then children.flatMap collect else #[stx]
    | _ => #[]

/-- The value of the flag `use_floats` of a `cega [… use_floats …]` call: `false` for
`use_floats := false`, and `true` for `use_floats` and `use_floats := true`. -/
def useFloats (arguments : Syntax) : Bool :=
  -- The value is absent, or the keyword `true` or `false` under its token node.
  (arguments[2][1].find? fun stx ↦ stx.isAtom && stx.getAtomVal == "false").isNone

/-- The configuration items of `cega (prec := n) (depth := n) (panels := n)`. -/
syntax (name := cegaConfigured) (colGt Lean.Parser.Term.configItem)+ : cegaArgs

/--
`cega (prec := n) (depth := n) (panels := n)`

Bare `cega` with a precision policy for its box route: `(prec := n)` and the other items of the
explicit form set the precision of the query, and `(depth := n)` the depth of the subdivision
that bare `cega` tries when the first query does not prove the bound (two by default). As in the
explicit form, depth zero still bisects the box once. `(prec := n)`, `(digits := d)` and
`(depth := n)` also set the endpoint bits and the subdivision depth of FloatLib's `interval`, the
route after the box route. On an interval integral, `(panels := n)` fixes the number of
quadrature panels, which otherwise doubles from one until the bound holds, up to the option
`cega.maxIntegrationPanels`.
-/
tactic_extension tacticCega

/-- The arguments of the explicit box query `cega (cfg) [enclose bindings] expr`. -/
syntax (name := cegaEnclose)
  Lean.Parser.Term.optConfig " [" &"enclose" cegaIntervalBinding,* "] " term : cegaArgs

/--
`cega [enclose ...] expr`

Synthesize a certificate for `expr` on an exact rational box and use it to close the current
goal. The goal selects the projection: an enclosure for `EnclosedOn f s lo hi`, an upper bound
for `BoundOn f s c`, an absolute bound for `BoundOn (fun x ↦ |f x|) s c`, a midpoint
approximation for `ApproxOn f (fun _ ↦ c) s ε`, and the bound an ordinary goal on the box's
variables states (`f x ≤ c`, `c ≤ f x`, `|f x| ≤ c`, `a ≤ f x ∧ f x ≤ b`, `f x ∈ Set.Icc a b`).
The optional configuration group, for example `(prec := 40)`, selects the numerical precision
policy, and `(depth := n)` encloses after `n` levels of checked box refinement. `(arith := F)`
computes the enclosure with IEEE floats of the format `F` of FloatLib, as in
`cega (arith := binary64) [enclose x in [0, 1]] (Real.exp x)`, and `(arith := "exact")` with
exact rationals whatever the option `cega.arithmetic` is; the flag `use_floats` belongs to bare
`cega`. An empty coordinate list, as in `cega [enclose] Real.sqrt 2`, queries a closed
expression.
-/
tactic_extension tacticCega

end CAS.CEGA

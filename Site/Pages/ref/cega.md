+++
id = "cega"
kind = "tactic"
title = "cega"
summary = "Proves numerical bounds: inequalities on a box of real variables, closed constants and interval integrals."
forms = ["CAS.CEGA.tacticCega", "CAS.CEGA.cegaConfigured", "CAS.CEGA.cegaFast", "CAS.CEGA.cegaFloats", "CAS.Numerics.cegaBatch", "CAS.Numerics.cegaFastBatch"]
see_also = ["cega-query", "cega-using", "enclose", "nintegrate", "N", "cas", "options"]
guide = "tactics"
tutorials = ["proving", "trust"]
imports = ["CAS.Numerics.Tactic"]
+++

::: usage
`cega`
: proves a numerical bound: an inequality on real variables that the hypotheses bound by rationals, a bound on a closed constant, or a bound on an interval integral.
`cega (prec := ‹n›) (depth := ‹n›) (panels := ‹n›)`
: the same with the precision, the depth of subdivision and the number of integration panels set by hand.
`cega [fast]`
: tries finite certificates first, checked by compiled code when `cega.nativeCertificates` is on, and is bare `cega` otherwise.
`cega [use_floats]`
: rounds enclosure endpoints outward into binary64. `cega [use_floats] (arith := ‹F›)` chooses
: the IEEE format ‹F›, and `cega [use_floats := false]` selects exact rational endpoints.
`cega [batch := ‹n›]`
: proves a goal `∀ i : Fin m, p i` by checking ‹n› indices at a time in the kernel.
`cega [fast, batch := ‹n›]`
: the same, with the batches checked by compiled code when `cega.nativeCertificates` is on.
:::

`cega` is the tactic I use for numbers. A bound like $\sin x \le 0.85$ for $x \in [0, 1]$ is true, obvious from a plot and tedious to prove by hand. `cega` encloses the expression on the box that your hypotheses describe, compares the enclosure with the bound by exact rational arithmetic, and hands the kernel a certificate for the whole argument.

The name is short for *certified enclosures, guarantees and approximations*.

## Details and Options

- The goal is a bound: $f \le c$, $f < c$, $c \le f$, $\lvert f \rvert \le c$, a two-sided bound, `f ∈ Set.Icc a b` (also `Ioo`, `Ico`, `Ioc`), $f \le g$, or a conjunction of these.
- Every real variable needs rational bounds among the hypotheses: `a ≤ x` and `x ≤ b`, `x ∈ Set.Icc a b`, or `|x| ≤ r`. A goal without variables needs none.
- When the first enclosure is too weak, the box is cut in halves, by default to depth 2. `(depth := n)` sets that depth.
- A bound on one interval integral with rational limits, such as $\int_a^b f \le c$ or $\lvert \int_a^b f - c \rvert \le \varepsilon$, uses Simpson panels when the first four derivatives of $f$ are certified on $[a, b]$, and range panels, which need only continuity, otherwise. The number of panels doubles up to `cega.maxIntegrationPanels`, by default 256, and `(panels := n)` fixes it.
- A real inequality that the box route does not prove goes to FloatLib’s `interval`, which reads the bounds in the hypotheses itself and is not limited by `cega.maxDimension`. It also proves bounds on finite sums, and it bounds a trigonometric polynomial in one variable by its coefficients, with no bounds on the variable. With floats on, it is not run, since it computes with exact rationals.
- A closed goal that these routes refuse is tried with the tactic `dyadic_interval` at 32 bits, or at the bits of `(prec := n)`.
- The [certificate propositions](guide:certificates) `EnclosedOn`, `BoundOn` and `ApproxOn` of SymLean are goals too.
- The functions are those of [[N]], written as Mathlib terms such as `Real.sin x` and `Real.sqrt x`. The box route takes at most 8 variables (`cega.maxDimension`).
- `set_option cega.nativeCertificates true` lets the `fast` forms check finite certificates with compiled code. That also trusts Lean’s compiler, so it is off by default and every check stays in the kernel.
- `[use_floats]` rounds each lower endpoint toward $-\infty$ and each upper endpoint toward
  $+\infty$ into binary64, and the kernel evaluates every operation. `(arith := F)` selects
  another IEEE binary format of FloatLib, such as
  `binary32`, `binary128`, `FloatFormat.ieee 15 112` or `"binary(p := 113, emax := 16383)"`,
  and turns floats on by itself. The flag shares its bracket group with `fast`, as in
  `cega [fast, use_floats]`.
- `set_option cega.arithmetic "binary64"` sets the default arithmetic. A call can override it:
  `cega [use_floats := false]` and the explicit query with `(arith := "exact")` both use exact
  endpoints. [Certificates](guide:certificates#arithmetic) shows how to set the default in Lake.
- When the goal states its bound with numerals, bare `cega` first tries FloatLib’s check, a
  refutation of the negation of the bound that bisects the box where it needs to, within
  `cega.maxRefinementWork` evaluations, and then the box query. With floats on, the query is the
  plain interval evaluation, on a uniform subdivision of depth `(depth := n)`. In a float format
  neither has the monotonicity argument of the exact planner, so a sharp bound needs some room or
  a larger depth. A bound on an integral is computed with exact rationals and is not run. A float
  call that does not prove its goal fails with the format and the reason, and never computes with
  rationals in its place.
- `cega [batch := n]` and `cega [fast, batch := n]` need `import CAS.Numerics.Tactic`.
- A false bound, or a true one that the enclosures do not reach, is refused, and the message proposes the next call to try.

## Examples

### Basic Examples

A bound on a box, from the hypotheses on `x`:

```lean
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x ≤ 0.85 := by
  cega
```

---

A bound on a constant:

```lean
example : Real.exp 1 ≤ 2.72 := by
  cega
```

---

A bound on an integral with no elementary antiderivative:

```lean
example : (∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) ≤ 3 / 4 := by
  cega
```

### Scope

A strict two-sided bound, and membership in an open interval:

```lean
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 < x * (1 - x) + 1 ∧ x * (1 - x) + 1 < 2 := by
  cega
```

```lean
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ∈ Set.Ioo (-1 : ℝ) 1 := by
  cega
```

---

Several bounds at once. The three expressions differ, so each bound is proved on its own:

```lean
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 ≤ x / (1 + x) ∧ Real.exp x ≤ 3 ∧ |Real.sin x| < 1 := by
  cega
```

---

A hypothesis `|x| ≤ r` gives the box $[-r, r]$. Here it also keeps the denominator away from zero:

```lean
example (x : ℝ) (hx : |x| ≤ 1 / 2) : 1 / (1 - x) ≤ 2 := by
  cega
```

---

A trigonometric polynomial needs no bounds on its variable. FloatLib’s `interval` bounds $\sin x + \tfrac{1}{2} \cos 2x$ by its coefficients, $1 + \tfrac{1}{2}$:

```lean
example (x : ℝ) : Real.sin x + Real.cos (2 * x) / 2 ≤ 3 / 2 := by
  cega
```

---

Integrals with the limits reversed, and with an integrand that has a corner:

```lean
example : (∫ x in (1 : ℝ)..0, Real.exp x) < -1 := by
  cega
```

```lean
example : 1 / 2 < ∫ x in (-1 : ℝ)..1, |x| := by
  cega
```

### Options

`(panels := 2)` fixes the number of Simpson panels instead of doubling them:

```lean
example : |(∫ x in (0 : ℝ)..1, Real.exp x) - 17182818 / 10000000| ≤ 1 / 10000 := by
  cega (panels := 2)
```

---

`(depth := 3)` allows the box to be cut in halves to depth 3:

```lean
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  cega (depth := 3)
```

---

`cega [fast]` with the default settings is bare `cega`, checked in the kernel:

```lean
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * x ≤ 1 := by
  cega [fast]
```

---

`[use_floats]` computes the same bound with binary64 floats, and `(arith := binary128)` with binary128:

```lean
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.72 := by
  cega [use_floats]
```

```lean
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.72 := by
  cega (arith := binary128)
```

---

With floats, `(depth := 5)` evaluates the sine on 32 pieces of $[0, 1]$:

```lean
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x ≤ 0.85 := by
  cega [use_floats] (depth := 5)
```

---

A finite statement, checked three indices at a time, and then four at a time with the `fast` form:

```lean
example : ∀ i : Fin 10, i.val * i.val < 100 := by
  cega [batch := 3]
```

```lean
example : ∀ i : Fin 10, i.val * i.val < 100 := by
  cega [fast, batch := 4]
```

### Applications

`cega` proves the numerical fact and `linarith` finishes. Only the three standard axioms are used:

```lean
theorem cega_sin_lt_one (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x < 1 := by
  have h : Real.sin x ≤ 17 / 20 := by cega
  linarith

#print axioms cega_sin_lt_one
```

---

The digits that [[N]] prints, as a bound:

```lean
example : Real.sqrt 2 ≤ 1.415 := by
  cega
```

### Properties and Relations

[[cega-query|`cega?`]] proves the goal and tells you the explicit query that did it:

```lean
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x ≤ 0.85 := by
  cega?
```

---

That query is the one [[enclose]] runs, and it prints the interval behind the proof:

```lean
#cas [enclose x in [0, 1]] (sin x)
```

---

[[cas]] tries the same box route on ordinary inequalities:

```lean
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x ≤ 0.85 := by
  cas
```

### Possible Issues

A false bound is refused. Here $\sin 1 > 0.84$:

```lean error
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x ≤ 0.8 := by
  cega
```

---

No hypothesis bounds $x$ here, so there is no box. The bound holds for every real $x$, since $x(1 - x) = \tfrac{1}{4} - (x - \tfrac{1}{2})^2$, and `nlinarith [sq_nonneg (x - 1 / 2)]` proves it:

```lean error
example (x : ℝ) : x * (1 - x) ≤ 1 / 4 := by
  cega
```

---

Too few panels. The message gives the interval that the search proposes and the call to try next:

```lean error
example : |(∫ x in (0 : ℝ)..1, Real.exp x) - 17182818 / 10000000| ≤ 1 / 10000 := by
  cega (panels := 1)
```

---

An overflow. $10^{200}$ fits within binary64’s finite range but its square does not, so the
call fails and names the format. `cega (arith := binary128)` and plain `cega` prove this bound:

```lean error
example : (10 : ℝ) ^ 200 * 10 ^ 200 ≤ 10 ^ 401 := by
  cega [use_floats]
```

---

Thirty digits of $\sqrt 2$ are more than binary64 has. `cega (arith := binary128)` proves this one:

```lean error
example : Real.sqrt 2 ≤ 1.41421356237309504880168872421 := by
  cega [use_floats]
```

---

A batch that fails names its indices. A failed batch is not a counterexample. Either the check did not reduce to `true`, as here, or the kernel reached its recursion limit, and then the message proposes a larger `maxRecDepth` or smaller batches:

```lean error
example : ∀ i : Fin 2, i.val = 0 := by
  cega [batch := 1]
```

### Neat Examples

The examples from here on run after `open CAS.Certificate`.

The exact range of $x/(1+x^2)$ on $[-2, 2]$, stated as a certificate proposition on a box in $\mathbb{R}^1$. The first query falls short, and bare `cega` then bisects to depth 2, which cuts $[-2, 2]$ at 0 and at the turning points $\pm 1$:

```lean hidden
open CAS.Certificate
```

```lean
example :
    EnclosedOn (fun p : ℝ^1 ↦ p 0 / (1 + p 0 ^ 2)) {p | -2 ≤ p 0 ∧ p 0 ≤ 2}
      (-1 / 2 : ℝ) (1 / 2 : ℝ) := by
  cega
```

---

The cosine on a short interval near 100:

```lean
example (x : ℝ) (h0 : 100 ≤ x) (h1 : x ≤ 100001 / 1000) : 0.86 ≤ Real.cos x := by
  cega
```

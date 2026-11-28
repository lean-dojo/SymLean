+++
id = "derive"
kind = "mode"
title = "derive"
summary = "The derivative of an expression, with the conditions it needs and a theorem about Mathlib’s `HasDerivAt`."
forms = ["CAS.Command.casDerivativeCommand", "CAS.Command.casUnivariateDerivativeCommand"]
see_also = ["grad", "integrate", "series", "limit", "cas"]
tutorials = ["first-hour", "proving"]
+++

::: usage
`#cas [derive ‹x›] ‹e›`
: gives the derivative $\partial e / \partial x$ of ‹e› with respect to ‹x›, with the conditions under which it holds. Every other variable of ‹e› is a parameter.
`#cas [derive] ‹e›`
: differentiates ‹e› in its only variable, or a function `fun ‹x› ↦ ‹e›` in its parameter.
:::

`derive` computes a derivative and gives its `HasDerivAt` statement. You get the derivative printed the way you would write it, and under it the theorem SymLean proved: a statement about Mathlib’s `HasDerivAt` for the real functions, with every condition it needs as a hypothesis. For me those conditions are as much a part of the answer as the derivative. The derivative of $\sqrt{2x + 2}$ is claimed only where $2x + 2 > 0$, and the derivative of $1/x$ only where $x \ne 0$.

## Details and Options

- The theorem has the form $\forall x,\; c_1 \to \dots \to c_k \to \operatorname{HasDerivAt}\,(\lambda x.\, e)\; e'\; x$, where $e'$ is the printed derivative and $c_1, \dots, c_k$ are the conditions. `HasDerivAt f f' x` is Mathlib’s statement that $f$ has the derivative $f'$ at $x$. Lean’s kernel checks its proof before the report appears.
- The functions are `abs`, `sin`, `cos`, `tan`, `sinh`, `cosh`, `tanh`, `atan`, `asin`, `acos` (also written `arctan`, `arcsin`, `arccos`), `exp`, `log` and `sqrt`, with `+`, `-`, `*`, `/` and powers. A power with a variable exponent, such as `x ^ y`, is a real power.
- The error function `erf` is differentiated only in sums and differences of at most eight terms `c * erf (A * x + B)`, where `c`, `A` and `B` do not contain $x$: numbers such as `2`, `1/2` or `sqrt 2`, `π`, or parameters such as `a`, for all of whose real values the theorem holds. The theorem is about SymLean’s `CAS.erf` (see [[erf]]), since Mathlib v4.36.0 has no error function.
- A square root contributes a condition $a > 0$ and a quotient a condition $d \ne 0$. A logarithm contributes $a \ne 0$ (Mathlib’s real logarithm is total, and its derivative theorem holds on both sides of $0$), the base of a real power $a > 0$, and `asin` and `acos` the conditions $a \ne -1$ and $a \ne 1$. Lean’s division is total ($1/0 = 0$), so a derivative of $1/x$ is only claimed where $x \ne 0$.
- The “Conditions” line of the report prints the conditions in a display form, which can differ from the hypothesis of the theorem. For `sqrt (2 * x + 2)` the line reads $x + 1 > 0$, and the theorem has `0 < 2 * x + 2`.
- For the functions other than `erf`, “The certificate” shows the theorem first, followed by the steps for SymLean’s internal expressions, from which it is transported. When the proof of the theorem takes more than its own budget of `maxHeartbeats` heartbeats, the report leaves the theorem out and keeps only the internal steps.
- A function `fun t ↦ e` is differentiated in its parameter. Name it, as in `#cas [derive t]`, or leave the name out.
- `set_option cas.verbose true` adds the tree of differentiation rules to the report: each rule with its input and its raw derivative.
- `set_option cas.suggest true` adds the theorem as an `example` you can paste into your file in place of the command.
- The tactic [[cas]] proves the same `HasDerivAt` and `deriv` goals, so a derivative you found here can go straight into a proof.
- Mathlib’s `deriv` is total: at a point where the function is not differentiable it is `0`. For the bare functions `abs`, `Real.log`, `Real.sinh`, `Real.cosh` and `Real.tan`, [[cas]] applies Mathlib’s `deriv` lemmas, which hold at every point, so it proves equalities such as `deriv Real.log 0 = 0⁻¹` (both sides are `0`) without a validity check. A `HasDerivAt` goal, by contrast, states differentiability.

## Examples

### Basic Examples

The derivative of $x^2 \sin x$:

```lean
#cas [derive x] (x ^ 2 * sin x)
```

---

A square root needs a positive argument, and the report says so. Its “Conditions” line prints the hypothesis `0 < 2 * x + 2` of the theorem as $x + 1 > 0$:

```lean
#cas [derive x] (sqrt (2 * x + 2))
```

---

With one variable you can leave its name out:

```lean
#cas [derive] (x ^ 3)
```

### Scope

Every variable other than the one you name is a parameter:

```lean
#cas [derive x] (sin (x * y))
```

---

The trigonometric, hyperbolic and inverse functions come with the conditions Mathlib’s theorems need:

```lean
#cas [derive x] (tan x)
```

```lean
#cas [derive x] (arcsin x)
```

```lean
#cas [derive x] (sinh x)
```

---

The absolute value is differentiable away from 0. The condition is stated as $x^2 > 0$:

```lean
#cas [derive x] (|x|)
```

---

Powers with a real or a negative exponent. A negative integer exponent is read as the reciprocal of a natural power, so the second theorem is about `1 / x ^ 2`:

```lean
#cas [derive x] (x ^ (3/2 : ℝ))
```

```lean
#cas [derive x] (x ^ (-2))
```

```lean
#cas [derive x] (x ^ y)
```

---

The error function, whose derivative is a Gaussian. The theorem is about SymLean’s `CAS.erf`:

```lean
#cas [derive x] (erf x)
```

---

A function is differentiated in its parameter:

```lean
#cas [derive] (fun x ↦ a * x + b)
```

### Options

With `cas.suggest`, the report ends with the theorem as an `example`, ready to paste:

```lean
set_option cas.suggest true in
#cas [derive x] (tan x)
```

---

Here it is pasted, and `cas` proves it:

```lean
example (x : ℝ) (h : Real.cos x ≠ 0) :
    HasDerivAt (fun x ↦ Real.tan x) (1 / Real.cos x ^ 2) x := by
  cas
```

---

With `cas.verbose`, “The computation” shows every differentiation rule that was applied:

```lean
set_option cas.verbose true in
#cas [derive x] (sqrt (2 * x + 2))
```

### Applications

A derivative in a proof. The tactic `cas` proves the statement, and only the three standard axioms are used:

```lean
theorem derive_product (x : ℝ) :
    HasDerivAt (fun x ↦ x ^ 2 * Real.sin x) (2 * x * Real.sin x + x ^ 2 * Real.cos x) x := by
  cas

#print axioms derive_product
```

---

The critical points of $x^3 - 3x$: differentiate, then solve $f'(x) = 0$:

```lean
#cas [derive x] (x ^ 3 - 3 * x)
```

```lean
#cas [solve x] (3 * x ^ 2 - 3 = 0)
```

### Properties and Relations

The gradient collects the partial derivatives:

```lean
#cas [grad x, y] (x ^ 2 * y + y ^ 3)
```

```lean
#cas [derive y] (x ^ 2 * y + y ^ 3)
```

---

Differentiating an antiderivative gives back the integrand:

```lean
#cas [integrate x] (x * sin (x ^ 2))
```

```lean
#cas [derive x] (-(1/2) * cos (x ^ 2))
```

### Possible Issues

Only the functions listed above are differentiated. The Gamma function is not one of them:

```lean error
#cas [derive x] (gamma x)
```

---

The error function is differentiated only in the sums described above. A product with it is refused:

```lean error
#cas [derive x] (x * erf x)
```

---

The name in brackets has to be the parameter of the function:

```lean error
#cas [derive x] (fun t : ℝ ↦ t ^ 2)
```

---

Without a name, the expression must have exactly one variable:

```lean error
#cas [derive] (x * y)
```

---

A condition is part of the answer. Here the theorem says nothing at $x = 0$, where Lean’s $1/0 = 0$ makes $1/x$ a function with no derivative:

```lean
#cas [derive x] (1 / x)
```

### Neat Examples

A rational function with a degree 6 denominator:

```lean
#cas [derive x] (1 / (x ^ 6 + 3 * x ^ 4 + 4 * x ^ 3 + 2 * x ^ 2 + 5 * x + 3))
```

---

A combination of error functions:

```lean
#cas [derive x] (2 * erf (3 * x + 1) - erf (x / 2))
```

---

The function $x^x$:

```lean
#cas [derive x] (x ^ x)
```

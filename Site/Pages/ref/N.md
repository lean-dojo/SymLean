+++
id = "N"
kind = "mode"
title = "N"
summary = "The first digits of a closed real expression, with a theorem that every printed digit is right."
forms = ["CAS.Command.casDigitsCommand"]
see_also = ["enclose", "nintegrate", "findRoot", "cega", "options"]
guide = "numerics"
tutorials = ["first-hour", "trust"]
+++

::: usage
`#cas [N ‹d›] ‹e›`
: gives the first ‹d› significant digits of the closed real expression ‹e›, truncated toward zero, with a theorem that they are the digits of the real number.
:::

`N` returns a decimal approximation and a theorem enclosing the exact value of ‹e› between that decimal and the next one away from zero. The theorem is about Mathlib’s `Real.pi`, `Real.exp` and `Real.sqrt`, and Lean’s kernel checks its proof. For $\sqrt 2$ to six digits the theorem is $1.41421 \le \sqrt 2 < 1.41422$.

## Details and Options

- For a positive value whose printed digits form the integer $m$, the theorem is $m / 10^k \le e < (m+1)/10^k$. For a negative value it is $-(m+1)/10^k < e \le -m/10^k$. A value with more than ‹d› digits before the decimal point has $m \cdot 10^k$ in place of $m / 10^k$.
- The digits are read from an interval that encloses the value. For a value with a short decimal expansion, such as $\cos(\pi/3) = \tfrac{1}{2}$, the interval can fail to decide them. When four doublings of the working precision do not settle them, the report proves a decimal enclosure $lo/10^k \le e \le hi/10^k$ instead.
- ‹e› has no variables. It may use rational arithmetic, integer powers, `sqrt`, `exp`, `log`, `sin`, `cos`, `tan`, `atan`, `asin`, `acos` (also written `arctan`, `arcsin`, `arccos`), the hyperbolic functions, real powers with a positive base, and the constants `pi` (or `π`) and `E`.
- `BesselJ n q`, `erf q` and the orthogonal polynomials at a rational point $q$ have routes of their own. For `BesselJ` and `erf` the report gives a decimal enclosure of width at most $10^{-d}$, and ‹d› is at most 30.
- ‹d› lies between 1 and the option `cas.maxDigits`, which is 2000 unless you set it.
- The tactic [[cega]] proves the bounds that the digits imply, such as `Real.sqrt 2 ≤ 1.415`.

## Examples

### Basic Examples

The square root of 2 to 20 digits:

```lean
#cas [N 20] (sqrt 2)
```

---

A sum of two constants:

```lean
#cas [N 10] (exp 1 + pi)
```

---

Fifty digits of $\pi$:

```lean
#cas [N 50] (pi)
```

### Scope

Trigonometric values, and an inverse function:

```lean
#cas [N 30] (sin 1)
```

```lean
#cas [N 30] (sin (π / 7))
```

```lean
#cas [N 30] (arcsin (1 / 2))
```

---

A cube root, written as a real power:

```lean
#cas [N 30] (2 ^ (1 / 3 : ℝ))
```

---

A negative value. Its digits are truncated toward zero too:

```lean
#cas [N 25] (-log 2)
```

---

A large value gets an exponent:

```lean
#cas [N 20] (exp 100)
```

---

The error function and a Bessel function have their own series. The report gives a decimal enclosure of width at most $10^{-d}$ and the number of terms of the series:

```lean
#cas [N 10] (erf (1/2))
```

```lean
#cas [N 10] (BesselJ 0 1)
```

---

An orthogonal polynomial at a rational point has an exact value, and you get it together with its digits:

```lean
#cas [N 10] (ChebyshevT 5 (1/3))
```

### Applications

Digits in a proof. `cega` proves a bound that the printed digits of $\sqrt 2$ imply. Only the three standard axioms are used:

```lean
theorem digits_sqrt_two : Real.sqrt 2 ≤ 1.415 := by
  cega

#print axioms digits_sqrt_two
```

---

A constant from a closed form. Here is $\arctan \tfrac{1}{3} + \log 3 + \sqrt 5$ to 40 digits:

```lean
#cas [N 40] (atan (1 / 3) + log 3 + sqrt 5)
```

### Properties and Relations

[[enclose]] gives an interval with rational endpoints instead of digits. Its precision is set by `(prec := n)`:

```lean
#cas [enclose] (sqrt 2)
```

```lean
#cas (prec := 16) [enclose] (sqrt 2)
```

---

The value $\cos(\pi/3) = \tfrac{1}{2}$ has a short decimal expansion, and the report gives an enclosure. Every interval around $\tfrac{1}{2}$ that the evaluator finds holds numbers starting with 0.4 and numbers starting with 0.5, so no truncated digit can be proved:

```lean
#cas [N 20] (cos (pi / 3))
```

### Possible Issues

`N` evaluates closed expressions only. For an expression with a variable, [[enclose]] works on a box:

```lean error
#cas [N 15] (x + 1)
```

---

At least one digit, and at most `cas.maxDigits`:

```lean error
#cas [N 0] (pi)
```

```lean error
set_option cas.maxDigits 10 in
#cas [N 20] (pi)
```

---

The series of `erf` and `BesselJ` stop at 30 digits:

```lean error
#cas [N 31] (erf 1)
```

---

Lean defines `Real.log 0 = 0`, but `N` evaluates a logarithm only when it has certified that the argument is positive:

```lean error
#cas [N 10] (log 0)
```

### Neat Examples

A thousand digits of $\pi$, each one proved:

```lean
#cas [N 1000] (pi)
```

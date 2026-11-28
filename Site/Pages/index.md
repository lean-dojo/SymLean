+++
id = "home"
kind = "home"
title = "SymLean"
tagline = "A verified computer algebra system in Lean."
authors = ["Robert Joseph George", "Changhe Yang", "Peicong Song", "Thomas Y. Hou", "Anima Anandkumar"]
affiliation = "Caltech"
summary = "SymLean is a verified computer algebra system in Lean. It computes integrals, derivatives, limits, series, sums, roots and numerical bounds, and every answer comes with a theorem that Lean checks."
+++

::: figure #teaser class="teaser"
```lean
#cas [integrate x] (atan x)
```
Caption: An antiderivative of $\arctan x$, with the Lean theorem underneath. Open the certificate to follow the differentiation step by step.
:::

## Introduction {#introduction}

Computer algebra systems such as Mathematica, Maple and SymPy have long been part of how we do mathematics. Whether we are deriving an equation, working out an integral or simplifying a particularly unpleasant expression, it is often much easier to ask a computer to do the calculation. But when formalizing mathematics in Lean, we still need to prove that the resulting expression is correct. This can take considerably more effort than finding the answer itself. SymLean grew out of our interest in making these two processes work together. We wanted something that feels like a conventional computer algebra system but produces Lean theorems that we can use directly in our proofs.

The library covers symbolic algebra, differentiation, integration, series expansions, limits, equation solving, special functions and certified numerical computation. Calculations can be performed interactively using [[cas-command|`#cas`]] or within an existing Lean proof using the [[cas]] and [[cega]] tactics.

An important distinction is that the algorithms used to find an answer do not themselves need to be trusted. They can be heuristic, and we can even delegate computations to external computer algebra systems. Consider, for instance, the integral of $1/x^2$ over $[-1,1]$. Mathematica has previously returned $-2$ for this integral, even though it diverges. Interestingly, our own search also finds $-2$! The difference is that [SymLean cannot certify this answer](guide:why#same-inputs): the argument requires a nonzero denominator throughout the interval, which is not the case here.

## What can we compute? {#what}

Much of the interface should feel familiar to anyone who has worked with Mathematica or SymPy. We can factor a polynomial, integrate a function, compute a Taylor expansion or find the roots of an equation with a single command. Below are a few examples from different parts of the library. Variables in these commands are interpreted as real numbers, so we do not need to declare them beforehand.

::: figure #six-examples
::: grid
### Algebra
```lean
#cas [factor] (2*x^3 - 3*x^2 + 1)
```
### Calculus
```lean
#cas [integrate x in [0, 1]] (x * exp x)
```
### Series and limits
```lean
#cas [series x 0 7] (sin x)
```
### Equations
```lean
#cas [roots x] (x ^ 5 - x - 1 = 0)
```
### Special functions
```lean
#cas (zeta 4)
```
### Certified numerics
```lean
#cas [nintegrate x in [0, 1]] (exp (-x^2))
```
:::
Caption: The quintic root and the Gaussian integral come back as decimals, and the statements underneath give their error bounds.
:::

The last two numerical examples are particularly useful in formal proofs. Rather than simply returning a decimal approximation, SymLean establishes a precise bound on the quantity being computed. This is something we frequently need when formalizing arguments in analysis, differential equations and scientific computing.

The [getting started guide](tutorial:first-hour) covers how to use these commands in your own Lean files, and the [[docs|documentation]] goes into more detail on the algorithms, options and supported operations.

## From computation to proof {#pipeline}

Finding a mathematical expression and checking that it is correct are often two very different problems. Integration is perhaps the most familiar example: finding an antiderivative can be quite difficult, while checking one usually amounts to differentiation and simplification. We make use of this asymmetry throughout SymLean.

::: figure #pipeline-figure svg="pipeline.svg"
Caption: Finding the antiderivative is the search step. Differentiating it gives Lean something it can check.
:::

For the integral at the top of this page, the search finds the candidate

$$F(x)=x\arctan(x)-\frac12\log(1+x^2).$$

A verified differentiator computes its derivative, and a verified normalizer establishes that $F'(x)-\arctan(x)=0$. We can then use the fundamental theorem of calculus to obtain the corresponding result for any finite interval.

There are also some interesting subtleties when working with symbolic expressions in a theorem prover. Division in Lean, for instance, is a total operation, with $1/0=0$. This means that seemingly straightforward simplifications can require additional hypotheses. Take

$$\frac{x^4-1}{x^2-1}=x^2+1.$$

We would ordinarily cancel the common factor and move on. In Lean, however, the equality is false at $x=1$ and $x=-1$. SymLean therefore includes the necessary condition $x^2-1\neq 0$ in the resulting theorem.

```lean
#cas [simplify] ((x ^ 4 - 1) / (x ^ 2 - 1))
```

These conditions are particularly important when symbolic calculations form part of a larger mathematical argument, where a missing hypothesis can invalidate much more than the calculation itself.

## What do we need to trust? {#trust}

By default, the proofs produced by SymLean are checked by Lean's kernel and depend only on the three standard axioms used throughout Mathlib: `propext`, `Classical.choice` and `Quot.sound`. We can inspect this ourselves using `#print axioms`.

```lean
theorem integral_x_exp : ∫ x in (0 : ℝ)..1, x * Real.exp x = 1 := by
  cas

#print axioms integral_x_exp
```

This separation between computation and verification gives us considerable freedom in how we implement the search algorithms. We can experiment with different symbolic methods, use numerical heuristics or call external software without adding those implementations to our trusted computing base.

For larger computations, SymLean also provides an optional [[options|native-certificate mode]]. This uses compiled evaluation to check finite certificates more efficiently, at the cost of additionally trusting Lean's compiler. The option is disabled by default, and the additional axiom is visible through `#print axioms`. We discuss these choices and their implications in more detail in the [documentation](tutorial:trust).

## Mathlib and other computer algebra systems {#relations}

SymLean is intended to complement existing mathematical software rather than replace it. There is already decades of excellent work on symbolic computation, and we would like to make more of it accessible from within formal mathematics.

::: figure #architecture-figure svg="architecture.svg"
Caption: Dashed arrows are proposals, which nobody has to trust. SymLean turns them into certificates and proofs with Mathlib and FloatLib, and Lean's kernel checks the result.
:::

**Mathlib.** All of our results are expressed using Mathlib's mathematical definitions, including its notions of derivatives, interval integrals, special functions and matrices. This allows the resulting theorems to be used directly in existing formalizations. Internally, SymLean also makes extensive use of established Mathlib tactics such as `ring`, `field_simp`, `norm_num`, `positivity` and `linarith`.

**External computer algebra systems.** Through [DSLean](https://github.com/taterowney/DSLean) and the optional [[oracle|`CASOracle`]] library, SymLean can work with SymPy, SageMath, Maxima, PARI/GP, FLINT, Giac, Singular and Gappa. These systems can do much of the computationally difficult work of finding a result, while SymLean constructs the corresponding proof. SymPy and SageMath cover most of the modes, from integrals and factorizations to Gröbner bases, equations, sums and differential equations. Maxima and Giac integrate, PARI/GP and FLINT factor polynomials and find their roots, Singular computes Gröbner bases and ideal memberships, doing the work of Mathlib's `polyrith` with a local tool, and Gappa proposes the interval bounds that [[cega]] checks.

```lean quote=tests/oracle/Oracles.lean
#cas [factor, oracle := pari] (x ^ 6 - 1)
```

In this example, we certify the factorization identity returned by PARI/GP, but not the irreducibility of the individual factors. The distinction is reflected in the output.

**Hex.** [Hex](https://github.com/leanprover/hex), the Lean FRO's library of verified computational algebra, proves factorization, determinants and primality in Lean itself. On Lean 4.35, SymLean called it for Berlekamp–Zassenhaus factoring, Bareiss determinants and primality certificates, and that route comes back as soon as Hex is released for Lean 4.36. We are in touch with its developers.

## Why are we interested in this? {#why}

As we formalize more mathematics, particularly in areas such as analysis, differential equations and numerical analysis, symbolic and numerical calculations become increasingly difficult to avoid. A substantial part of a proof may consist of calculations that would ordinarily be delegated to mathematical software. We have encountered this ourselves while working on the formalization of partial differential equations. Sometimes the mathematical argument is already well understood, and the remaining difficulty is simply getting a long calculation through Lean.

There is also an interesting opportunity here for AI-assisted mathematics. LLMs are becoming increasingly capable of finding mathematical arguments and proposing symbolic manipulations, but verifying the intermediate calculations remains important. A computer algebra system that produces formal proofs could be useful both to mathematicians working interactively and to AI systems exploring new proofs. We hope SymLean will make this kind of work a little easier.

## Credits {#credits}

SymLean is developed at Caltech by Robert Joseph George, Changhe Yang, Peicong Song, Thomas Y. Hou and Anima Anandkumar. The library builds on [Mathlib](https://github.com/leanprover-community/mathlib4), uses [FloatLib](https://github.com/lean-dojo/FloatLib) for certified numerical computation and integrates with external computer algebra systems through [DSLean](https://github.com/taterowney/DSLean). SymLean is also used in [PDEAtlas](https://github.com/lean-dojo/PDEAtlas), our ongoing effort to formalize partial differential equations.

Many thanks to the Lean and Mathlib communities for the mathematical foundations, software and helpful discussions. SymLean is open source under the [Apache 2.0 license](https://github.com/lean-dojo/SymLean/blob/main/LICENSE). Contributions, feedback and suggestions for new mathematical applications are very welcome.

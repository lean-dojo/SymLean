+++
id = "oracles"
kind = "guide"
title = "Oracles"
summary = "SymPy, SageMath, Maxima, PARI/GP, FLINT, Giac, Singular and Gappa as untrusted search, with every proposal proved in Lean or refused."
related_guides = ["tactics", "certificates"]
tutorials = ["trust"]
+++

A mature computer algebra system is very good at search, and I don’t need to trust it to use it. With the optional library `CASOracle`, a command or the tactic `cas` asks an external tool for a proposal: an antiderivative, a factorization, cofactors, a solution, a closed form, a sum of squares or digits. SymLean then proves the statement from the proposal with its own checkers, and the kernel checks the proof. A proposal that doesn’t check is refused, so a bug in the tool can cost you an answer, but it can’t give you a false theorem.

::: commands
### Asking a tool
- oracle
### In proofs
- cas
- cas-integrate-primitive
### Settings
- options
:::

The requests and the answers go through [DSLean](https://github.com/taterowney/DSLean), by taterowney and the DSLean contributors. The [[oracle]] page lists the tools, what each one is asked, and how to build the library.

In a proof, `cas [oracle := o]` suggests a proof to keep in place of the call. For a definite integral the suggestion is `cas [integrate primitive := F]` with the oracle’s antiderivative, for an equation that follows from the hypotheses it is a `linear_combination`, and for an inequality between polynomials it is the script that proved the goal. None of these needs the oracle. In two cases the proof still does: a membership in an ideal gets no suggestion, and an inequality whose script doesn’t check as printed, for instance because an atom prints as `x✝`, gets the call itself. Here SymPy finds how the goal follows from the hypotheses, and the proof you keep doesn’t need SymPy:

```lean quote=tests/oracle/Oracles.lean suggestion
theorem combination_by_sympy (x y : ℝ) (h1 : x * y = 1) (h2 : x = y) : x ^ 2 = 1 := by
  cas [oracle := sympy]
```

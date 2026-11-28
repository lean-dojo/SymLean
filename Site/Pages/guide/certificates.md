+++
id = "certificates"
kind = "guide"
title = "Certificates"
summary = "The statements behind the numerics: enclosures, bounds and approximations on a box, the carriers that hold them, the tactics that prove and reuse them, and certificates on tables of any size."
related_guides = ["numerics", "tactics"]
tutorials = ["trust", "proving"]
imports = ["CAS.Cert.Reduce", "CAS.Examples.Cert.Seed"]
+++

CEGA stands for Certified Enclosures, Guarantees, and Approximations. I wanted a numerical result to be a statement you can read and use like any other, so its statements are ordinary propositions about real functions on a set, and each one has a fixed meaning:

::: table
Statement | Meaning
`EnclosedOn f s lo hi` | $\mathrm{lo} \le f(x) \le \mathrm{hi}$ for every $x \in s$
`BoundOn f s hi` | $f(x) \le \mathrm{hi}$ for every $x \in s$
`ApproxOn f g s ε` | $\lVert f(x) - g(x) \rVert \le \varepsilon$ for every $x \in s$
`ResidualBound r s ε` | $\lVert r(x) \rVert \le \varepsilon$ for every $x \in s$
:::

A carrier, such as `EnclosureCert`, `BoundCert`, `ApproxCert`, `ResidualCert`, `ModelApproxCert` or `QuadratureCert`, keeps the function, the domain, the bounds and a proof of its statement. Anything else it holds, such as the order of a model, is data and proves nothing. Only the proved statement counts.

::: commands
### Proving the statements
- cega
- enclose
### Reusing a carrier
- cega-using
### Asking for the call to keep
- cega-query
### Settings
- options
:::

The examples on this page run after `open CAS.Certificate`. `ℝ^n` is our notation for Mathlib’s `EuclideanSpace ℝ (Fin n)`, and `p 0` is the first coordinate of a point `p`.

```lean hidden
open CAS.Certificate
```

The explicit form of `cega` names the box and the expression. The bounds you state may be weaker than the ones it computes, and exact arithmetic covers the difference:

```lean
example :
    EnclosedOn (fun p : ℝ^1 ↦ p 0 / (1 + p 0))
      {p : ℝ^1 | 0 ≤ p 0 ∧ p 0 ≤ 1} 0 (1 / 2) := by
  cega [enclose x in [0, 1]] (x / (1 + x))
```

When the domain is a box with rational bounds, bare `cega` reads the function and the box off the goal, so you don’t have to repeat them:

```lean
example :
    BoundOn (fun p : ℝ^2 ↦ p 0 * p 1)
      {p : ℝ^2 | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 2 ≤ p 1 ∧ p 1 ≤ 3} 4 := by
  cega
```

In practice, most uses need no certificate statement at all. On an inequality whose variables have rational bounds in the context, `cega` builds the certificate itself and carries it to the goal, as in [[numerics|Numerics]].

## Exact rationals or IEEE floats {#arithmetic}

By default `cega` computes its enclosures with exact integers and rationals. People also want
enclosures in the IEEE format their numbers live in, so `cega` has a switch. With `[use_floats]`
the two ends of every interval are finite binary64 values. In the kernel,
[FloatLib](https://github.com/lean-dojo/FloatLib) computes a rational enclosure at each operation
and rounds its lower end toward $-\infty$ and its upper end toward $+\infty$. The theorem doesn’t
change. It is still about real numbers, and it uses the same three axioms:

```lean
theorem exp_le_floats (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.72 := by
  cega [use_floats]

#print axioms exp_le_floats
```

`(arith := F)` picks the format: `binary16`, `binary32`, `binary64`, `binary128`, `FloatFormat.ieee e f` for `e` exponent bits and `f` fraction bits, or a format named by its precision and its largest exponent, as in `(arith := "binary(p := 113, emax := 16383)")`. It turns floats on by itself, so `cega (arith := binary128)` needs no flag. `set_option cega.arithmetic "binary64"` does the same for every call after it, and [[cega-query|`cega?`]] names the arithmetic that a proof used.

### One line for a whole build {#arithmetic-build}

A project usually wants one arithmetic for all its proofs, and nobody wants to edit every call. `cega.arithmetic` is an ordinary Lean option, so the lakefile can set it. In `lakefile.toml` that is one line under `[leanOptions]`:

```
[leanOptions]
weak.cega.arithmetic = "binary64"
```

In `lakefile.lean` it is ``leanOptions := #[⟨`weak.cega.arithmetic, "binary64"⟩]``. When the value comes from a configuration option, the command line chooses the arithmetic:

```lean quote=tests/floats/consumer/lakefile.lean
def arithmetic : String := (get_config? arithmetic).getD "exact"
```

```lean quote=tests/floats/consumer/lakefile.lean
lean_lib Bounds where
  leanOptions := #[⟨`weak.cega.arithmetic, arithmetic⟩]
```

With this lakefile, `lake build` computes with exact rationals and `lake build -R -Karithmetic=binary64` with binary64 floats, and no Lean file changes in between. The prefix `weak.` makes Lean skip the option in a module that doesn’t import SymLean. Lake hands the option to Lean as `-Dweak.cega.arithmetic=binary64`, and the same flag on the command line of `lean` sets it for one file. A call that chooses for itself keeps its choice in every build: `cega [use_floats := false]` is exact, `cega (arith := binary128)` is binary128, and the explicit query takes `(arith := "exact")`. `tests/floats` builds a small package both ways and reads back which computation each proof contains.

### What a format can’t prove {#arithmetic-limits}

A float end lies a little further out than the rational one, and a format has a largest number. So a true bound can be out of reach of a format. When that happens the call fails, names the format and the reason, and proposes a wider format or exact arithmetic. It never computes with rationals in its place:

```lean error
example : (10 : ℝ) ^ 200 * 10 ^ 200 ≤ 10 ^ 401 := by
  cega [use_floats]
```

$10^{200}$ fits within binary64’s finite range, but its square doesn’t. `cega (arith := binary128)`
proves this bound, and so does plain `cega`. Thirty digits of $\sqrt 2$ go the same way, for
want of precision rather than range: binary64 has about sixteen, and binary128 about thirty-four.

The method differs too. When the goal states its bound with numerals, bare `cega` first tries
FloatLib’s check, a refutation of the negation of the bound that bisects the box where it needs
to, within `cega.maxRefinementWork` evaluations, and then the box query. With floats the query
is the plain interval evaluation, on a uniform subdivision of the box when you give
`(depth := n)`. The exact route also has a planner that uses monotonicity and centered forms,
which is how it gets the sharp $x(1 - x) \le \tfrac{1}{4}$ on $[0, 1]$. Floats prove that bound
with a little room, `≤ 0.26` at `(depth := 6)`, and not without it. A bound on an integral is
computed with exact rationals, so it isn’t run with floats.

### What it costs {#arithmetic-cost}

In `tests/floats/measure.tsv`, the rows of one run of `tests/floats/measure.py`, exact
arithmetic takes less kernel time than every float format that proves the same goal, both for
single `cega` calls and for repeated interval evaluations. FloatLib computes each float operation in
exact rationals and then rounds the result outward into the format. The routes don’t do the
same work either: the exact planner can use that sine is increasing on $[0, 1]$, while the float
query may need subdivisions. So speed isn’t what floats are for. They give you the computation
in an IEEE format: the certified ends are numbers of the format, and the numbers keep a fixed
size. Exact arithmetic gives you the sharp bounds, the integrals and no overflow.

## Certificates of any size {#large}

`cega` proves one bound on one box. A computer-assisted proof often rests on much more data than that: a table of coefficients, a bound on every cell of a mesh, anything from a few numbers to hundreds of gigabytes. For this SymLean has a small framework, `CAS.Cert`. `import CAS` doesn’t load it, so the examples below also import `CAS.Cert.Reduce` and `CAS.Examples.Cert.Seed`, and they run after `open CAS.Cert CAS.Numerics`.

```lean hidden
open CAS.Cert CAS.Numerics
```

I wanted the statement and its test to be written once, whatever the size of the data and whatever evaluates the test. So a condition is a term of one small language, `Cond`: comparisons of real expressions in the data, `and`, `or`, `all n` for every index below `n`, and `onIcc` for every real point of a cell. Its test computes on balls, each a center and a radius in natural numbers, and one theorem, `Cond.holds_of_check`, says that a passing test proves the condition for all real data that the balls enclose. On a goal without data, `cert_cond` writes the condition for you, and the kernel runs the test:

```lean
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
    Real.exp (x * y) + x ^ 2 ≤ 4 := by
  cert_cond
```

The size of the data changes only who evaluates the test. There are four regimes, with the same condition and the same theorem in each:

::: table
Regime | What evaluates the test | What you trust
1 | the kernel, in one module | the kernel
2 | the kernel, in many modules that one theorem joins | the kernel
3 | the same modules under [[options|`cega.nativeCertificates`]] | Lean’s compiler as well
4a | any of these three, on tables recomputed from a seed | what that regime trusts
4b | a program that reads the files | the program and the files; the run is a hypothesis of the theorem
:::

`tests/cert/measure.py` compares these modes on synthetic data using one condition: on each cell
of a mesh, the cubic of the cell is at most the bound of the cell at every real point of the cell.
Each cell stores its four coefficients and its bound, or recomputes them from a seed in regime 4a.
`tests/cert/measure.tsv` holds the rows of one run.

When a single module gets too large, `cert_shard` states one range of indices in a module of its
own, `cert_aggregate` joins the ranges, and `scripts/CertStubs.lean` writes the modules from a
manifest. `cert_shard` checks its batches one after the other, so a module of tests needs the
memory of one batch, not of all of them, and `tests/cert/build.sh` sets two variables of the C
library’s allocator so that the memory of one batch is kept for the next.

### The final theorem assumes a certificate {#nonempty}

When the data are too large to appear in a statement, the final theorem doesn’t mention them. It assumes `Nonempty T`, where `T` is a type of certificates stated over the real numbers, and a verified checker supplies `Nonempty T` from any input that it accepts. The interface is `Check C`: a Boolean `run` with a proof that `run = true` implies `C`. Checks combine like the statements they prove, with `Check.and`, `Check.all`, `Check.onCover` and the others, and `Check.nonempty_of_run` is the pattern as a theorem. Here a certificate is an integer $z$ such that the square of $z / 10^6$ is within $10^{-5}$ of $2$, and the checker tests the integer it is given:

```lean
/-- A certificate: an integer `z` with the square of `z / 10 ^ 6` within `10⁻⁵` of `2`. -/
structure RootCert where
  z : ℤ
  near : |((z : ℝ) / 1000000) ^ 2 - 2| ≤ 1 / 100000

/-- The same statement as a condition on one stored number. -/
def rootCond : Cond Unit :=
  .le (absE (.sub (.pow (Cond.dat ()) 2) (.nat 2))) (.rat 1 100000)

/-- The checker: for an integer `z`, the test of `rootCond` on the ball of `z / 10 ^ 6`. -/
def rootCheck (z : ℤ) : Check (Nonempty RootCert) :=
  ⟨rootCond.run 64 fun _ ↦ .ofFrac 64 (decide (z < 0)) z.natAbs 1000000, fun h ↦
    ⟨⟨z, by
      simpa [rootCond, Cond.holds, eval_absE] using
        Cond.holds_of_run (fun _ ↦ GridBall.enclosesReal_ofFrac 64 z 1000000) rootCond
          (fun _ ↦ 0) h⟩⟩⟩

theorem root_cert : Nonempty RootCert :=
  Check.nonempty_of_run rootCheck ⟨1414214, by cert_eval [rootCheck, rootCond]⟩

#print axioms root_cert
```

The kernel evaluated the test, so `root_cert` uses the three standard axioms. An input that is not close to a root, such as `1500000`, makes the test fail and proves nothing. The type is small enough to inhabit by hand, so it shows only the shape. In a real proof the fields of `T` are the numerical hypotheses of the final theorem.

### Recomputing a table instead of storing it {#seed}

A test never sees a table. It sees a function from an index to a ball, and the theorem asks only that each ball encloses the real entry. So the balls can be computed when they are read, and a table that follows from a small seed doesn’t have to exist anywhere. In `CAS/Examples/Cert/Seed.lean` the seed is four coefficients of a cubic, each known within $2^{-30}$. The tables of a mesh of 256 cells are recomputed from it at every read, and the kernel tests the cells in four declarations. The result holds for the whole family of seeds:

```lean
open CAS.Examples.Cert in
#check @Seed.cubic_le
```

When the true entries are only close to what the generator computes, `widen` enlarges each ball by an error bound, which the theorem then assumes, as `Seed.value_le` does.

### A run over files is a hypothesis {#run}

Past what a build can embed, a program reads the files part by part and runs the same test. Lean has no proof that such a run happened, and I didn’t want an axiom for it. So `Run.Ok m family` is a proposition: there are byte strings with the lengths and SHA-256 digests of the manifest `m` on which the test of every shard passes. A theorem that uses a run takes it as a hypothesis, where you can see it:

```lean
open CAS.Examples.Cert MeshSpec in
example (m : Run.Manifest) (h : Run.Ok m test) :
    ∃ texts, Run.Matches m texts ∧
      ∀ k < m.count, ∀ σ, (cellCond k).holds (storedVal (Run.look m texts)) σ :=
  cells_of_run h
```

The conclusion is about the tables of byte strings with those digests, and `holds_cellCond` unfolds the condition of a cell to the inequality on the cell. Whoever asserts `Run.Ok` after a run trusts the program that evaluated the test, the reading of the files and the script that started it, and `TRUST.md` has the whole list. `CAS/Examples/Cert/Mesh.lean` proves `Run.Ok` in the kernel for seven short byte strings, so the hypothesis can be met.

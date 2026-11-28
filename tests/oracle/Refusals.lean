/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

import CASOracle.DSolve
import CASOracle.Factor
import CASOracle.Ideal
import CASOracle.Numeric
import CASOracle.Sum

/-!
# The trust boundary: wrong, broken and missing oracles are refused

`tests/oracle/run.sh` runs this file with the programs of `tests/oracle/drivers/` in place of the
real ones: a Python that answers every `sympy` task plausibly but wrongly (except three sums of
squares and one Gröbner basis, which it gets right so that their scripts and the accepted answer
can be pinned), never answers for `flint`, and prints garbage for `pari`; a Maxima whose answers
are outside the checked language, use an undeclared variable, or are too large to read; a Gappa
that leaves a child holding its output open; a Giac whose answers are wrong, outside the checked
language, not the lists a task expects, too long, or on the wrong stream (one family is right,
so that the numbering of its constants can be pinned); and a Singular whose answers are wrong,
are not polynomials, come in the wrong order, or are the messages of a run that stopped with an
error. `SYMLEAN_SAGE_PATH` names a program that does not exist. Every deliberately invalid
response must be refused with its reason. The last sections
check the axiom audit of the acceptance boundary, the acceptance of a right basis with a zero
element, and that the proofs the tactics and the commands suggest replay without any oracle, also
in sections whose variables could change what the printed text means.
-/

set_option linter.hashCommand false

/-! ## Wrong answers -/

/-- error: integrate: the primitive proposed by sympy, (x + 1)*exp(x), is refused -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := sympy] (x * exp x)

/-- error: factor: the factorization proposed by sympy -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := sympy] (x ^ 4 + 4)

/-- error: cas [oracle := sympy]: the cofactors proposed by sympy are refused -/
#guard_msgs (error, substring := true) in
example (x y : ℝ) (h1 : x * y = 1) (h2 : x = y) : x ^ 2 = 1 := by
  cas [oracle := sympy]

/-- error: groebner: the basis proposed by sympy is refused -/
#guard_msgs (error, substring := true) in
#cas [groebner x, y, oracle := sympy] [x ^ 2 + y ^ 2 - 5, x * y - 2]

-- The inputs themselves, with the identity as cofactors both ways: they span the ideal but are
-- not a Gröbner basis, and the check of the Gröbner property refuses them.
/--
error: groebner: the basis proposed by sympy is refused: it is not shown to be a Gröbner basis
  groebner: the basis is not a Gröbner basis for `MonomialOrder.lex`: the S-polynomial of
-/
#guard_msgs (error, substring := true, whitespace := lax) in
#cas [groebner x, y, oracle := sympy] [x ^ 2 - y, y ^ 2 - x]

-- The proposed sum of squares is `(x + y) ^ 2`, which is not `x ^ 2 + y ^ 2`.
/-- error: cas [oracle := sympy]: the sum of squares proposed by sympy is refused -/
#guard_msgs (error, substring := true) in
example (x y : ℝ) : 0 ≤ x ^ 2 + y ^ 2 := by
  cas [oracle := sympy]

-- The proposed sum is `x ^ 2` itself: the identity holds, but no term is positive.
/--
error: cas [oracle := sympy]: the sum of squares proposed by sympy is refused: no term is a
positive constant or a positive constant times strict premises
This says nothing about the inequality.
-/
#guard_msgs in
example (x : ℝ) : 0 < x ^ 2 := by
  cas [oracle := sympy]

-- Under `x ≠ 0`, `positivity` would prove `0 < x ^ 2` from the same proposed sum `x ^ 2`, and the
-- polynomial is positive there. But no term of the sum has the accepted form, a positive constant
-- or a positive constant times strict premises, so the check of the strict form refuses it
-- before `positivity` runs.
/--
error: cas [oracle := sympy]: the sum of squares proposed by sympy is refused: no term is a
positive constant or a positive constant times strict premises
This says nothing about the inequality.
-/
#guard_msgs in
example (x : ℝ) (hx : x ≠ 0) : 0 < x ^ 2 := by
  cas [oracle := sympy]

-- The multiplier `1 + y ^ 2` turns `(x * y - 1) ^ 2 + x ^ 2` into `1 + (x - y + x * y ^ 2) ^ 2`;
-- the proposed `y ^ 2` does not.
/-- error: cas [oracle := sympy]: the sum of squares proposed by sympy is refused -/
#guard_msgs (error, substring := true) in
example (x y : ℝ) : 0 < (x * y - 1) ^ 2 + x ^ 2 := by
  cas [oracle := sympy]

/-- error: solve: no solution proposed by sympy could be checked -/
#guard_msgs (error, substring := true) in
#cas [solve x, y, oracle := sympy] (x ^ 2 + y ^ 2 = 5 ∧ x * y = 2)

/-- error: nsolve: no root proposed by sympy could be certified (refused: [0.500000, 2.000000]) -/
#guard_msgs (error, substring := true) in
#cas [nsolve x in [0, 1], oracle := sympy] (cos x = x)

-- 2 is a root of x = 2, but outside the interval asked for; 0.5 is no root.
/-- error: nsolve: no root proposed by sympy could be certified (refused: [0.500000, 2.000000]) -/
#guard_msgs (error, substring := true) in
#cas [nsolve x in [0, 1], oracle := sympy] (x = 2)

/-- error: nintegrate: the value 0.750000 proposed by sympy could not be certified -/
#guard_msgs (error, substring := true) in
#cas [nintegrate x in [0, 1], oracle := sympy] (exp (-x ^ 2))

/-- error: eigenvalues: no eigenvalue proposed by sympy could be certified -/
#guard_msgs (error, substring := true) in
#cas [eigenvalues, oracle := sympy] !![2, 1; 1, 3]

/-- error: sum: the closed form proposed by sympy -/
#guard_msgs (error, substring := true) in
#cas [sum k 1 n, oracle := sympy] (k)

/-- error: dsolve: the family proposed by sympy -/
#guard_msgs (error, substring := true) in
#cas [dsolve y x, oracle := sympy] (y' = y)

-- The zero function solves `y' = 1 / y` only through `1 / 0 = 0`: its condition `0 ≠ 0` fails.
/-- error: dsolve: the conditions of the family proposed by sympy fail at every test point -/
#guard_msgs (error, substring := true) in
#cas [dsolve y x, oracle := sympy] (y' = 1 / y)

/-! ## Broken and missing oracles -/

/-- error: oracle flint did not answer within 3000 ms -/
#guard_msgs (error, substring := true) in
set_option cas.oracle.timeout 3000 in
#cas [factor, oracle := flint] (x ^ 2 - 1)

/-- Whether the processes `pids` have all exited (polled for up to three seconds, so that the
init process can reap orphans). -/
def allGone (pids : List String) : IO Bool := do
  for _ in [0:300] do
    let mut alive := false
    for pid in pids do
      let out ← IO.Process.output { cmd := "ps", args := #["-o", "stat=", "-p", pid] }
      let state := out.stdout.trimAscii.toString
      unless state.isEmpty || state.startsWith "Z" do alive := true
    unless alive do return true
    IO.sleep 10
  return false

-- The program of that timeout ignored `SIGTERM` and left a child that ignores it too: both were
-- ended with the process group (`SIGKILL` after `SIGTERM`).
/-- info: program and child ended: true -/
#guard_msgs in
#eval show IO Unit from do
  let some file ← IO.getEnv "SYMLEAN_TEST_PIDFILE" | IO.println "no pid file"
  let pids := ((← IO.FS.readFile file).trimAscii.toString.splitOn " ")
  IO.println s!"program and child ended: {← allGone pids}"

-- The cleanup DSLean's runner uses on every exit path, `terminateGroup`, on a group whose leader
-- ignores `SIGTERM` and has forked a child that ignores it too (an ignored signal is inherited):
-- the `SIGKILL` that `killGroup` sends through the system `kill` ends both.
/-- info: SIGTERM-resistant group ended: true -/
#guard_msgs in
#eval show IO Unit from do
  let child ← IO.Process.spawn
    { cmd := "sh", args := #["-c", "trap '' TERM; sleep 60 & sleep 60"], stdin := .null,
      stdout := .null, stderr := .null, setsid := true }
  IO.sleep 300
  DSLean.terminateGroup child
  let mut gone := false
  for _ in [0:300] do
    -- `pgrep` exits with 1 exactly when no process matches; other codes are errors.
    let out ← IO.Process.output { cmd := "pgrep", args := #["-g", toString child.pid] }
    if out.exitCode == 1 && out.stdout.trimAscii.isEmpty then
      gone := true
      break
    IO.sleep 10
  IO.println s!"SIGTERM-resistant group ended: {gone}"

/-- error: oracle pari failed -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := pari] (x ^ 2 - 1)

/-- error: the oracle's answer is refused: it is outside the checked language -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := maxima] (exp (-x ^ 2))

/-- error: the oracle's answer is refused: it uses z, which is not a variable of the request -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := maxima] (x ^ 2 - 1)

/-- error: oracle maxima has no checkable answer: maxima left the integral unevaluated -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := maxima] (exp (x ^ x))

-- Answers that are expensive to read are refused before DSLean parses them (a long number, a
-- deep nesting, a long text) or before they are reflected (a tower of `tanh`, which the reifier
-- lowers by repeating its argument four times); an over-long chain of operations is refused by
-- DSLean's own depth bound.
/-- error: the oracle's answer is refused: a number in it is too long -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := maxima] (x)

/-- error: the oracle's answer is refused: it nests deeper than 512 -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := maxima] (x ^ 2)

/-- error: the oracle's answer is refused: it has over 20000 characters -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := maxima] (cos x)

/-- error: the oracle's answer is refused: its reflection would have over 20000 nodes -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := maxima] (sin x)

/-- error: the oracle's answer is refused: it is nested or chained more than 1000 deep -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := maxima] (x ^ 3)

-- A child of Gappa holds both output streams open; the group is ended with Gappa, the answer
-- arrives at once, and it is wrong.
/-- error: enclose: the enclosure [0.000000, 0.100000] proposed by gappa could not be certified -/
#guard_msgs (error, substring := true) in
set_option cas.oracle.timeout 20000 in
#cas [enclose x in [0, 1], oracle := gappa] (x)

/-- error: oracle maxima has no checkable answer: maxima has no solve -/
#guard_msgs (error, substring := true) in
#cas [solve x, oracle := maxima] (x = 1)

-- Sage has no task `sos`. It is refused before it is asked, so the refusal does not end with
-- "This says nothing about the inequality.".
/-- error: cas [oracle := sage]: oracle sage has no checkable answer: sage has no sos -/
#guard_msgs in
example (x : ℝ) : 0 ≤ x ^ 2 := by
  cas [oracle := sage]

/-- error: oracle sage is unavailable -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := sage] (x ^ 2 - 1)

/-- error: unknown oracle mathematica; use sympy, sage, pari, flint, maxima, giac, singular or gappa -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := mathematica] (x ^ 2 - 1)

/-! ## Giac

Giac's records are read on its standard error, and each holds the value of one command as Giac
prints it: an expression, a list of points, or one or several solution families. -/

/-- error: integrate: the primitive proposed by giac, x*exp(x) + exp(x), is refused -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := giac] (x * exp x)

/-- error: the oracle's answer is refused: it is outside the checked language -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := giac] (exp (-x ^ 2))

/-- error: oracle giac has no checkable answer: giac left the integral unevaluated -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := giac] (exp (x ^ x))

-- The right record, on standard output: it is not read there, and the run has no answer. The
-- refusal quotes the script as it was sent, the settings and one print.
/--
error: oracle giac failed: exit code 0, no answer: 0>> maple_mode(0):; complex_mode:=0:; approx_mode:=0:; angle_radian:=1:; threads:=1:;
1>> print("@@ antiderivative "+string(integrate(cos( v0 ), v0))):;
@@ antiderivative sin(v0)
(the standard error is empty or is not UTF-8)
-/
#guard_msgs (error, substring := true, whitespace := lax) in
#cas [integrate x, oracle := giac] (cos x)

/-- error: oracle giac is unavailable: the program did not run -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := giac] (sin x)

/-- error: the oracle's answer is refused: it uses x, which is not a variable of the request -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := giac] (x ^ 2)

-- A command that stops prints no record; the refusal quotes the end of both streams.
/--
error: oracle giac failed: exit code 0, no answer: 0>> maple_mode(0):; complex_mode:=0:; approx_mode:=0:; angle_radian:=1:; threads:=1:;
1>> print("@@ antiderivative "+string(integrate(v0, v0))):;
Error: Bad Argument Value
-/
#guard_msgs (error, substring := true, whitespace := lax) in
#cas [integrate x, oracle := giac] (x)

-- More on standard error than is kept (16 MiB): the answer would be cut, so the run is refused.
/-- error: oracle giac failed: the answer is over 16777216 bytes -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := giac] (x ^ 3)

-- A record `failed` on standard error is the failure of the run.
/-- error: oracle giac failed: giac gave up -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := giac] (x ^ 4)

/-- error: sum: the closed form proposed by giac, n^2/2, is refused -/
#guard_msgs (error, substring := true) in
#cas [sum k 1 n, oracle := giac] (k)

/-- error: sum: the closed form proposed by giac is refused: the oracle's answer is refused: it is outside the checked language -/
#guard_msgs (error, substring := true) in
#cas [sum k 1 n, oracle := giac] (1 / k)

/-- error: oracle giac has no checkable answer: giac left the sum unevaluated -/
#guard_msgs (error, substring := true) in
#cas [sum k 1 n, oracle := giac] (sin (k ^ 2))

/-- error: solve: no solution proposed by giac could be checked (refused: [x = 3, y = 1]) -/
#guard_msgs (error, substring := true) in
#cas [solve x, y, oracle := giac] (x ^ 2 + y ^ 2 = 5 ∧ x * y = 2)

/-- error: solve: giac reports no real solution (which proves nothing) -/
#guard_msgs (error, substring := true) in
#cas [solve x, oracle := giac] (x ^ 2 + 1 = 0)

-- A solution with a free parameter, here the unknown `y` itself, is no closed expression.
/-- error: the oracle's answer is refused: it uses v1, which is not a variable of the request -/
#guard_msgs (error, substring := true) in
#cas [solve x, y, oracle := giac] (x = y)

-- Giac answers this equation with a decimal.
/-- error: the oracle's answer is refused: it has a decimal number, outside the checked language -/
#guard_msgs (error, substring := true) in
#cas [solve x, oracle := giac] (x ^ 5 - x - 1 = 0)

/-- error: oracle giac failed: the answer is not a list of solutions: 1,2] -/
#guard_msgs (error, substring := true) in
#cas [solve x, oracle := giac] (x = 1)

/-- error: the oracle's solution 2 ; 3 does not have 1 values -/
#guard_msgs (error, substring := true) in
#cas [solve x, oracle := giac] (x = 2)

/-- error: oracle giac failed: the answer has 51 solutions, over 50 -/
#guard_msgs (error, substring := true) in
#cas [solve x, oracle := giac] (x = 3)

/-- error: oracle giac failed: the solution 4 is not a list of values -/
#guard_msgs (error, substring := true) in
#cas [solve x, oracle := giac] (x = 4)

/-- error: dsolve: the family proposed by giac, c1*exp(2*x), is refused -/
#guard_msgs (error, substring := true) in
#cas [dsolve y x, oracle := giac] (y' = y)

/-- error: oracle giac has no checkable answer: giac returned 2 solution families, not one -/
#guard_msgs (error, substring := true) in
#cas [dsolve y x, oracle := giac] (y' = y ^ 2)

/-- error: oracle giac has no checkable answer: giac found no solution family -/
#guard_msgs (error, substring := true) in
#cas [dsolve y x, oracle := giac] (y'' = y)

-- An equation of order one has the constant `c_0` only.
/-- error: dsolve: the family proposed by giac is refused: the oracle's answer is refused: it uses c_1, which is not a variable of the request -/
#guard_msgs (error, substring := true) in
#cas [dsolve y x, oracle := giac] (y' = 2 * y)

/-- error: dsolve: the conditions of the family proposed by giac fail at every test point -/
#guard_msgs (error, substring := true) in
#cas [dsolve y x, oracle := giac] (y' = 1 / y)

-- A right family, printed as a list of one family in Giac's second constant `c_1` only: it is
-- accepted with one constant, numbered `c1`.
/-- Output (a family of solutions (checked); that it is the general solution is not): y(x) = c1*sin(x) -/
#guard_msgs (info, substring := true) in
#cas [dsolve y x, oracle := giac] (y'' + y = 0)

/-- error: oracle giac has no checkable answer: giac has no factor -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := giac] (x ^ 2 - 1)

/-- error: oracle giac has no checkable answer: giac has no member -/
#guard_msgs (error, substring := true) in
example (x y : ℝ) (h1 : x * y = 1) (h2 : x = y) : x ^ 2 = 1 := by
  cas [oracle := giac]

/-! ## Singular

Singular's answers are read like Maxima's, and each must be a polynomial. A Singular that stops
with an error still exits with code 0; it has then printed no record. -/

/-- error: factor: the factorization proposed by singular, (x^2 - 2*x + 1)*(x^2 + 2*x + 2), is refused -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := singular] (x ^ 4 + 4)

/-- error: the oracle's answer is refused: it uses z, which is not a variable of the request -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := singular] (x ^ 2 - 1)

-- The messages of a Singular whose script failed, with exit code 0 and no record.
/-- error: oracle singular failed: exit code 0, no answer:    ? div. by 0 -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := singular] (x ^ 2 - 4)

/-- error: oracle singular is unavailable: the program did not run -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := singular] (x ^ 2 - 9)

/-- error: the oracle's factor sin(x) is not a polynomial -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := singular] (x ^ 2 - 16)

/-- error: groebner: the basis proposed by singular is refused: its cofactors do not prove that it spans the same ideal -/
#guard_msgs (error, substring := true) in
#cas [groebner x, y, oracle := singular] [x ^ 2 + y ^ 2 - 5, x * y - 2]

/-- error: oracle singular failed: the answer's basis and cofactor rows do not match -/
#guard_msgs (error, substring := true) in
#cas [groebner x, y, oracle := singular] [x ^ 2 - y, x * y - 1]

/-- error: cas [oracle := singular]: the cofactors proposed by singular are refused: linear_combination fails with them -/
#guard_msgs (error, substring := true) in
example (x y : ℝ) (h1 : x * y = 1) (h2 : x = y) : x ^ 2 = 1 := by
  cas [oracle := singular]

/-- error: the oracle's cofactor is refused: a cofactor is not a polynomial -/
#guard_msgs (error, substring := true) in
example (x : ℝ) (h : x ^ 2 = 4) : x = 2 := by
  cas [oracle := singular]

-- No power of `x - 3` up to the fourth is in the ideal of `x ^ 2 - 9`; the refusal is the
-- oracle's word and proves nothing.
/-- error: oracle singular has no checkable answer: singular found no power of the target up to 4 in the ideal -/
#guard_msgs (error, substring := true) in
example (x : ℝ) (h : x ^ 2 = 9) : x = 3 := by
  cas [oracle := singular]

open MvPolynomial in
/-- error: cas [oracle := singular]: the cofactors proposed by singular are refused -/
#guard_msgs (error, substring := true) in
example : (X 0 ^ 2 - 1 : MvPolynomial (Fin 2) ℚ) ∈ Ideal.span {X 0 * X 1 - 1, X 0 - X 1} := by
  cas [oracle := singular]

-- The task is checked before the request is written: Singular's grammar has no sine, and the
-- refusal is still that Singular has no such task.
/-- error: oracle singular has no checkable answer: singular has no integrate -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := singular] (sin x)

-- A quotient by a polynomial is no polynomial for `factor`, so Singular is not asked.
/-- error: factor: the input is not a polynomial with rational coefficients -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := singular] (x ^ 2 / x)

/-- error: cas [oracle := singular]: oracle singular has no checkable answer: singular has no sos -/
#guard_msgs in
example (x : ℝ) : 0 ≤ x ^ 2 := by
  cas [oracle := singular]

/-! ## Records

An answer counts only in the records its task expects, each as often as the task allows, from a
program that exited normally. -/

/-- error: oracle sympy failed: the answer has several records antiderivative -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := sympy] (cos x)

/-- error: oracle sympy failed: the answer has an unexpected record primitive -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := sympy] (sin x)

/-- error: oracle sympy failed: the oracle exited with code 3 after answering -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := sympy] (x ^ 3)

/-- error: oracle sympy failed: the answer has no record constant -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := sympy] (x ^ 2 - 4)

/-- error: the oracle's multiplicity 1234567890123 is not a small natural number -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := sympy] (x ^ 2 - 9)

/-- error: solve: sympy reports no real solution (which proves nothing) -/
#guard_msgs (error, substring := true) in
#cas [solve x, oracle := sympy] (x ^ 2 + 1 = 0)

/--
error: cas [oracle := sympy]: sympy found no sum of squares
This says nothing about the inequality.
-/
#guard_msgs in
example (x y z : ℝ) : 0 < x ^ 2 + y ^ 2 + z ^ 2 + 1 := by
  cas [oracle := sympy]

/-! ## Bounds on what is computed from an answer -/

-- A short answer whose constant has 2 ^ (10 ^ 12) as numerator is refused before any arithmetic.
/-- error: the oracle's answer is refused: its numbers could need over 100000 bits -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := maxima] (x ^ 2 - 4)

-- A real power whose exponent is a product of literals is a power with that exponent.
/-- error: the oracle's answer is refused: it has an exponent over 1000 -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := maxima] (x ^ 2 - 25)

-- Four constants of 30001 bits, each estimated at 90000: together they are over the budget of
-- the whole answer.
/-- error: the oracle's answer is refused: its numbers could need over 100000 bits -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := maxima] (x ^ 2 - 36)

/-- error: the oracle's answer has 201 factors, over 200 -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := maxima] (x ^ 2 - 16)

/-- error: the oracle's power 12345678901234 is not a small natural number -/
#guard_msgs (error, substring := true) in
example (x : ℝ) (h : x = 1) : x ^ 2 = 1 := by
  cas [oracle := sympy]

/-- error: the oracle's constant count 99999999999999 is not a small natural number -/
#guard_msgs (error, substring := true) in
#cas [dsolve y x, oracle := sympy] (y' = 2 * y)

/-- error: oracle sympy failed: the answer's basis and cofactor rows do not match -/
#guard_msgs (error, substring := true) in
#cas [groebner x, y, oracle := sympy] [x ^ 2 - y, x * y - 1]

/-- error: nsolve: sympy reports no real root (which proves nothing) -/
#guard_msgs (error, substring := true) in
#cas [nsolve x, oracle := sympy] (x ^ 2 + 1 = 0)

/-- error: eigenvalues: sympy reports no real eigenvalue (which proves nothing) -/
#guard_msgs (error, substring := true) in
#cas [eigenvalues, oracle := sympy] !![0, 1; -1, 0]

/-- error: oracle gappa failed: the oracle exited with code 2 after answering -/
#guard_msgs (error, substring := true) in
set_option cas.oracle.timeout 20000 in
#cas [enclose x in [0, 1], oracle := gappa] (x * x)

-- The derivative that the check of a primitive takes is admitted too.
/-- error: the oracle's answer is refused: its derivative: its expansion could form products of over 10000 terms -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := sympy] (x ^ 4)

/-- error: the oracle's answer is refused: its derivative: its numbers could need over 100000 bits -/
#guard_msgs (error, substring := true) in
#cas [integrate x, oracle := sympy] (x ^ 5)

-- Each factor is admitted, and so is the factorization with its multiplicities.
/-- error: the oracle's factorization is refused: its expansion could form products of over 10000 terms -/
#guard_msgs (error, substring := true) in
#cas [factor, oracle := sympy] (x ^ 2 - 49)

-- Powers written as products for Gappa are bounded before they are built.
/-- error: the request cannot be written for gappa: with its powers written as products it has over 20000 nodes -/
#guard_msgs (error, substring := true) in
#cas [enclose x in [0, 1], oracle := gappa] (((x ^ 64) ^ 64) ^ 64)

-- The reader of answers, directly: what it refuses and what it reads. Six nested `tanh` reflect
-- to 21841 nodes and are refused before reflection; five (5461 nodes) are refused by the bound on
-- the arguments of exponentials, since `tanh` is read through `exp`.
open Lean Elab Term in
/-- info: __import__('os').system('true'): it is outside the checked language (DSLean: Syntax error in input: unexpected trailing characters ('os').system('true'))
0.5*v0: it has a decimal number, outside the checked language
v0 + I: it uses I, which is not a variable of the request
v0;v0: it is outside the checked language (DSLean: Syntax error in input: unexpected trailing characters ;v0)
v0**2*sin(v0): read as x^2*sin(x)
2**3**2: read as 2^9
(v0**1000)**1000: its numbers could need over 100000 bits
v0**(1000+1): it has an exponent over 1000
((1**0+1**0)**1000)**100: its numbers could need over 100000 bits
tanh ×5: it has an exponential of an argument over 65536 in size
tanh ×6: its reflection would have over 20000 nodes
zero power of a tower: its numbers could need over 100000 bits
power with that exponent: its numbers could need over 100000 bits
2**log(exp(10^12)): it has an exponential of an argument over 65536 in size
v0**log(exp(1001)): it has a real power with an exponent over 1024 in size
(sin + sin + sin)**1000: its expansion could form products of over 10000 terms
(1+v0)**500*(1+v0)**500: its expansion could form products of over 10000 terms
2^96*(16 v0)**1000: its numbers could need over 100000 bits
log(exp(10^12)): it has an exponential of an argument over 65536 in size
tanh(v0): read as (exp(x) - exp(-x))/2/((exp(x) + exp(-x))/2)
exp(-v0**2): read as exp(-x^2)
exp(v0**3): read as exp(x^3)
1/(1 + exp(v0)): read as 1/(1 + exp(x))
(1 + v0)**100: read
(1 + v0)**1000: its expansion could take over 2000000 steps
(v0 - 1)*…*(v0 - 30): read
v0*(sin(1)+sin(2)+sin(3))**1000: its expansion could form products of over 10000 terms
log(exp(16384)**1000): its numbers could need over 100000 bits
log(exp(1/exp(-16))): it has an exponential of an argument over 65536 in size -/
#guard_msgs in
#eval show TermElabM Unit from do
  let tower (k : Nat) := String.join (List.replicate k "tanh(") ++ "v0" ++
    String.join (List.replicate k ")")
  for (label, text) in [("__import__('os').system('true')", "__import__('os').system('true')"),
      ("0.5*v0", "0.5*v0"), ("v0 + I", "v0 + I"), ("v0;v0", "v0;v0"),
      ("v0**2*sin(v0)", "v0**2*sin(v0)"), ("2**3**2", "2**3**2"),
      ("(v0**1000)**1000", "(v0**1000)**1000"), ("v0**(1000+1)", "v0**(1000+1)"),
      ("((1**0+1**0)**1000)**100", "((1**0+1**0)**1000)**100"), ("tanh ×5", tower 5),
      ("tanh ×6", tower 6),
      ("zero power of a tower", "((((2**1000)**1000)**1000)**1000)**0"),
      ("power with that exponent", "2**(((((2**1000)**1000)**1000)**1000)**0)"),
      ("2**log(exp(10^12))", "2**log(exp(1000*1000*1000*1000))"),
      ("v0**log(exp(1001))", "v0**log(exp(1001))"),
      ("(sin + sin + sin)**1000", "(sin(v0) + sin(2*v0) + sin(3*v0))**1000"),
      ("(1+v0)**500*(1+v0)**500", "(1 + v0)**500*(1 + v0)**500"),
      ("2^96*(16 v0)**1000", "(79228162514264337593543950336*(v0 + v0 + v0 + v0 + v0 + v0 + \
        v0 + v0 + v0 + v0 + v0 + v0 + v0 + v0 + v0 + v0))**1000"),
      ("log(exp(10^12))", "log(exp(1000000000000))"),
      ("tanh(v0)", "tanh(v0)"), ("exp(-v0**2)", "exp(-v0**2)"), ("exp(v0**3)", "exp(v0**3)"),
      ("1/(1 + exp(v0))", "1/(1 + exp(v0))"), ("(1 + v0)**100", "(1 + v0)**100"),
      ("(1 + v0)**1000", "(1 + v0)**1000"),
      ("(v0 - 1)*…*(v0 - 30)", "*".intercalate ((List.range 30).map (s!"(v0 - {· + 1})"))),
      ("v0*(sin(1)+sin(2)+sin(3))**1000", "v0*(sin(1) + sin(2) + sin(3))**1000"),
      ("log(exp(16384)**1000)", "log(exp(16384)**1000)"),
      ("log(exp(1/exp(-16)))", "log(exp(1/exp(-16)))")] do
    try
      let answer ← CASOracle.Translate.read `sympyIn (fun _ : Fin 1 ↦ "v0") text
      if label.startsWith "tanh ×" || label.startsWith "(1 + v0)" || label.startsWith "(v0 - 1)"
      then
        IO.println s!"{label}: read"
      else IO.println s!"{label}: read as \
        {(CAS.Command.FullSimplify.Form.ofExpr [`x] answer).tidy.render}"
    catch error =>
      let message ← error.toMessageData.toString
      let reason := ((message.splitOn "is refused: ").getLast!.splitOn "\n").headD message
      IO.println s!"{label}: {reason}"

-- Requests are written with every operation parenthesized and powers kept as powers (the
-- pattern of the product does not match a power through its unfolding).
open Lean Elab Term in
/-- info: ( v0 ** 2 )
( ( 1 / 3 ) - ( v0 ** ( 3 / 2 ) ) )
( ( v0 ^ 2 ) * %pi ) -/
#guard_msgs in
#eval show TermElabM Unit from do
  let v : CAS.Verified.Expr (Fin 1) := .var 0
  IO.println (← CASOracle.Translate.write `sympyOut (fun _ ↦ "v0") (.pow v 2))
  IO.println (← CASOracle.Translate.write `sympyOut (fun _ ↦ "v0") (.sub (.rat 1 3) (.rpow v (.rat 3 2))))
  IO.println (← CASOracle.Translate.write `maximaOut (fun _ ↦ "v0") (.mul (.pow v 2) .pi))

-- The reader of Giac's answers, directly: Giac writes `ln`, `pi` and `exp(1)`; what it prints
-- outside the checked language (special functions, algebraic numbers as `rootof`, the imaginary
-- unit, decimals, an unevaluated sum) is refused, and so are `e` and `log`, which it did not
-- print in our probes.
open Lean Elab Term in
/-- info: -1/6*ln(v0^2+v0+1)-sqrt(3)/3*atan((v0+1/2)/(sqrt(3)/2))+1/3*ln(abs(v0-1)): read as -1/6*log(x^2 + x + 1) - sqrt(3)/3*atan((x + 1/2)/(sqrt(3)/2)) + 1/3*log(|x - 1|)
exp(1)*v0: read as exp(1)*x
pi*v0^(1/3): read as pi*x^(1/3)
2^v0: read as 2^x
erf(v0): it is outside the checked language (DSLean: Syntax error in input: unexpected trailing characters (v0))
rootof([[1,0,-2],[1,0,-3]]): it is outside the checked language (DSLean: Syntax error in input: unexpected trailing characters ([[1,0,-2],[1,0,-3]]))
e*v0: it uses e, which is not a variable of the request
log(v0): it is outside the checked language (DSLean: Syntax error in input: unexpected trailing characters (v0))
i*v0: it uses i, which is not a variable of the request
infinity: it uses infinity, which is not a variable of the request
1/2*v0^2*sign(v0): it is outside the checked language (DSLean: Syntax error in input: unexpected trailing characters (v0))
Psi(v0+1)+euler_gamma: it is outside the checked language (DSLean: Syntax error in input: unexpected trailing characters (v0+1)+euler_gamma)
1.5*v0: it has a decimal number, outside the checked language
sum(sin(v0^2),v0,1,n0): it is outside the checked language (DSLean: Syntax error in input: unexpected trailing characters (sin(v0^2),v0,1,n0)) -/
#guard_msgs in
#eval show TermElabM Unit from do
  for text in ["-1/6*ln(v0^2+v0+1)-sqrt(3)/3*atan((v0+1/2)/(sqrt(3)/2))+1/3*ln(abs(v0-1))",
      "exp(1)*v0", "pi*v0^(1/3)", "2^v0", "erf(v0)", "rootof([[1,0,-2],[1,0,-3]])", "e*v0",
      "log(v0)", "i*v0", "infinity", "1/2*v0^2*sign(v0)", "Psi(v0+1)+euler_gamma", "1.5*v0",
      "sum(sin(v0^2),v0,1,n0)"] do
    try
      let answer ← CASOracle.Translate.read `giacIn (fun _ : Fin 1 ↦ "v0") text
      IO.println s!"{text}: read as \
        {(CAS.Command.FullSimplify.Form.ofExpr [`x] answer).tidy.render}"
    catch error =>
      let message ← error.toMessageData.toString
      let reason := ((message.splitOn "is refused: ").getLast!.splitOn "\n").headD message
      IO.println s!"{text}: {reason}"

-- The lists Giac prints are split at the commas that no bracket encloses; a text that is not a
-- list, or that closes more brackets than it opens, is none. The kinds of the brackets are not
-- compared, and an empty item is kept: the reader refuses such items.
/-- info: list[[1,2],[2,1]]: (some [[1,2], [2,1]])
[]: (some [])
[sqrt(-v0^2-2*c_0),-sqrt(-v0^2-2*c_0)]: (some [sqrt(-v0^2-2*c_0), -sqrt(-v0^2-2*c_0)])
[rootof([[1,0,-2],[1,0,-3]])]: (some [rootof([[1,0,-2],[1,0,-3]])])
c_0*exp(v0): none
1,2]: none
[1,2: none
[1,2]]: none
[1,2): none
[a]b: none
[(1]]: (some [(1]])
[a,]: (some [a, ])
a list of 1000001 characters: none -/
#guard_msgs in
#eval show IO Unit from do
  for text in ["list[[1,2],[2,1]]", "[]", "[sqrt(-v0^2-2*c_0),-sqrt(-v0^2-2*c_0)]",
      "[rootof([[1,0,-2],[1,0,-3]])]", "c_0*exp(v0)", "1,2]", "[1,2", "[1,2]]", "[1,2)", "[a]b",
      "[(1]]", "[a,]"] do
    IO.println s!"{text}: {CASOracle.Translate.listItems? text}"
  let long := "[" ++ String.ofList (List.replicate 999999 '1') ++ "]"
  IO.println s!"a list of {long.length} characters: {CASOracle.Translate.listItems? long}"

-- After the refused answers above, the tokens of the reading grammars are no keywords in this
-- file: `E` and `pi` are names like any other.
example (E pi : ℝ) : E + pi = pi + E := add_comm E pi

-- The scripts as they are sent. Giac: the settings, then one print of one value. Singular: the
-- ring, the procedures of `oracle/symlean_oracle.sing`, and the statements of the request inside
-- a procedure, which an error leaves.
/-- info: maple_mode(0):; complex_mode:=0:; approx_mode:=0:; angle_radian:=1:; threads:=1:;
print("@@ key "+string(command)):;
ring symleanR = 0, (v0, v1), lp;
short = 0;
option(redSB);
option(redTail);
(the procedures)
proc symleanAnswer()
{
  ideal I = a, b;
  poly f = t;
  symleanMember(f, I, 2, 4);
}
symleanAnswer();
quit;
factor:
  poly p = t;
  symleanFactor(p);
groebner:
  ideal I = a, b;
  symleanGroebner(I, 2); -/
#guard_msgs in
#eval show IO Unit from do
  let procedures := CASOracle.Script.singularProcedures.trimAscii.toString
  let statements (script : String) : String :=
    (((script.splitOn "proc symleanAnswer()\n{\n").getLast!).splitOn "\n}\n").head!
  IO.print (CASOracle.Script.giac "key" "command")
  IO.print ((CASOracle.Ideal.memberScript 2 "t" ["a", "b"] 4).replace procedures
    "(the procedures)")
  IO.println s!"factor:\n{statements (CASOracle.Factor.singularScript 1 "t")}"
  IO.println s!"groebner:\n{statements (CASOracle.Ideal.groebnerScript 2 ["a", "b"])}"

-- Requests to Singular: every real numeral and every divisor is cast to a rational `number`,
-- since Singular computes with integer literals as machine integers and divides polynomials with
-- the remainder dropped. A function or a real power cannot be written.
open Lean Elab Term in
/-- info: ( ( number( 1 ) / number( number( 3 ) ) ) * v0 )
( ( ( ( v0 ^ 3 ) / number( number( 2 ) ) ) - ( v0 ^ 2 ) ) + ( v0 / number( number( 2 ) ) ) )
( ( number( 2 ) ^ 31 ) * v0 )
(- number( 7 ) )
( v0 / number( ( v1 + number( 1 ) ) ) )
( number( 123456789012345678901234567890 ) * v0 )
the request cannot be written for the oracle: No matching pattern found for expression Real.sin v0
the request cannot be written for the oracle: No matching pattern found for expression v0 ^ (3 / 2) -/
#guard_msgs in
#eval show TermElabM Unit from do
  let v : CAS.Verified.Expr (Fin 2) := .var 0
  let w : CAS.Verified.Expr (Fin 2) := .var 1
  for request in [CAS.Verified.Expr.mul (.rat 1 3) v,
      .add (.sub (.div (.pow v 3) (.nat 2)) (.pow v 2)) (.div v (.nat 2)),
      .mul (.pow (.nat 2) 31) v, .int (-7), .div v (.add w (.nat 1)),
      .mul (.nat 123456789012345678901234567890) v, .sin v, .rpow v (.rat 3 2)] do
    try
      IO.println (← CASOracle.Translate.write `singularOut (fun i ↦ s!"v{i.val}") request)
    catch error =>
      IO.println (← error.toMessageData.toString)

-- A number at the depth where DSLean's writer stops (500 steps, 4 for a summand): the writer
-- falls back to the bare number, which Singular would read as a machine integer, so the request
-- is refused. With one summand fewer the number keeps its cast.
open Lean Elab Term in
/-- info: 123 summands: written, every number cast: true
124 summands: the request cannot be written for the oracle: one of its numbers lies deeper than DSLean's writer goes -/
#guard_msgs in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#eval show TermElabM Unit from do
  for k in [123, 124] do
    let request := (List.replicate k (CAS.Verified.Expr.var (0 : Fin 1))).foldl .add
      (.pow (.nat 2) 70)
    try
      let text ← CASOracle.Translate.request .singular "factor" (fun _ ↦ "v0") request
      IO.println s!"{k} summands: written, every number cast: \
        {CASOracle.Translate.numbersCast text}"
    catch error => IO.println s!"{k} summands: {← error.toMessageData.toString}"

-- The numbers of a request do not depend on the user's pretty-printer options.
open Lean Elab Term in
/-- info: ( ( v0 ** 2 ) + ( 1 / 3 ) ) -/
#guard_msgs in
set_option pp.numericTypes true in
set_option pp.explicit true in
#eval show TermElabM Unit from do
  IO.println (← CASOracle.Translate.write `sympyOut (fun _ : Fin 1 ↦ "v0")
    (.add (.pow (.var 0) 2) (.rat 1 3)))

-- Singular's answers are polynomials in Maxima's syntax, and `maximaIn` reads them.
open Lean Elab Term in
/-- info: 1/4*v1^2-5/4: read as 1/4*y^2 - 5/4
-v0*v1-2: read as -x*y - 2
2*v0+v1^3-5*v1: read as 2*x + y^3 - 5*y
17636684144620811271604938270*v0^3: read as 17636684144620811271604938270*x^3 -/
#guard_msgs in
#eval show TermElabM Unit from do
  for text in ["1/4*v1^2-5/4", "-v0*v1-2", "2*v0+v1^3-5*v1",
      "17636684144620811271604938270*v0^3"] do
    let answer ← CASOracle.Translate.read `maximaIn (fun i : Fin 2 ↦ s!"v{i.val}") text
    IO.println s!"{text}: read as \
      {(CAS.Command.FullSimplify.Form.ofExpr [`x, `y] answer).tidy.render}"

-- The expansion of a power of a sum of eleven terms in ten variables is bounded before any
-- expansion, also inside a function that simplification removes.
open Lean Elab Term in
/-- info: its expansion could form products of over 10000 terms
its expansion could form products of over 10000 terms -/
#guard_msgs in
#eval show TermElabM Unit from do
  for text in ["(1 + v0 + v1 + v2 + v3 + v4 + v5 + v6 + v7 + v8 + v9)**1000",
      "log(exp((1 + v0 + v1 + v2 + v3 + v4 + v5 + v6 + v7 + v8 + v9)**1000))"] do
    try
      discard <| CASOracle.Translate.read `sympyIn (fun i : Fin 10 ↦ s!"v{i.val}") text
      IO.println "read"
    catch error =>
      let message ← error.toMessageData.toString
      IO.println (((message.splitOn "is refused: ").getLast!.splitOn "\n").headD message)

-- Gappa's bounds are read exactly, annotations skipped; a box with a negative end is rounded
-- outward.
open Lean Elab Term in
/-- info: some ((-768614336404564651 : Rat)/2305843009213693952, (3 : Rat)/4)
{ v0 in [ - 0.3333333333333333333333334 , 0.1428571428571428571428572 ] -> sqrt( v0 ) in ? }
-/
#guard_msgs in
#eval show TermElabM Unit from do
  IO.println (repr (CASOracle.Translate.gappaBounds?
    "Results:\n  v0 * v0 - 1 / 3 in [-768614336404564651b-61 {-0.333333, -2^(-1.58496)}, \
      3b-2 {0.75, 2^(-0.415037)}]"))
  IO.print (← CASOracle.Translate.gappaProblem (fun _ : Fin 1 ↦ "v0") (fun _ ↦ (-1/3, 1/7))
    (.sqrt (.var 0)))

-- DSLean's runner: an output over its bound, an output that is not UTF-8, and cancellations.
/-- info: overflow 1000
not UTF-8
cancelled
cancelled -/
#guard_msgs in
#eval show IO Unit from do
  let describe (result : Except DSLean.RunFailure DSLean.RunResult) : String :=
    match result with
    | .error (.overflow bytes) => s!"overflow {bytes}"
    | .error .notUTF8 => "not UTF-8"
    | .error .cancelled => "cancelled"
    | _ => "unexpected"
  IO.println (describe (← DSLean.runProgram "sh" #["-c", "yes | head -c 100000"] ""
    { maxOutputBytes := 1000 }))
  IO.println (describe (← DSLean.runProgram "sh" #["-c", "printf '\\377'"]))
  let token ← IO.CancelToken.new
  token.set
  IO.println (describe (← DSLean.runProgram "sleep" #["5"] "" {} (some token)))
  -- A descendant that leaves the group holds standard output after the program has exited; a
  -- cancellation while the run waits for that output is reported as a cancellation.
  let later ← IO.CancelToken.new
  discard <| IO.asTask (do IO.sleep 300; later.set) .dedicated
  IO.println (describe (← DSLean.runProgram "sh" #["-c", "setsid sleep 3 & exit 0"] ""
    {} (some later)))

/-! ## The axiom audit

A proof through a fresh axiom is refused by `Accept.audit`, and a command whose evidence adds a
theorem through one is refused by `Accept.withAuditedEvidence`, its messages discarded. The
environment is restored afterwards. -/

open Lean Elab Command Meta in
/-- info: refused: the proof depends on [_testedAxiom (through _testedAxiom)] -/
#guard_msgs (info, substring := true) in
run_meta withoutModifyingEnv do
  let fact ← mkEq (← mkAppM ``HAdd.hAdd #[mkNatLit 2, mkNatLit 2]) (mkNatLit 4)
  addDecl <| .axiomDecl
    { name := `_testedAxiom, levelParams := [], type := fact, isUnsafe := false }
  try
    CASOracle.Accept.audit "audit" fact (mkConst `_testedAxiom)
    logInfo "accepted"
  catch error =>
    logInfo m!"refused: {(← error.toMessageData.toString).drop 7}"

open Lean Elab Command Meta in
/-- error: report: refused, the evidence depends on [_taintedAxiom] -/
#guard_msgs (error, substring := true) in
run_cmd CASOracle.Accept.withAuditedEvidence "report" do
  liftTermElabM do
    let fact ← mkEq (← mkAppM ``HAdd.hAdd #[mkNatLit 1, mkNatLit 1]) (mkNatLit 2)
    addDecl <| .axiomDecl
      { name := `_taintedAxiom, levelParams := [], type := fact, isUnsafe := false }
    addDecl <| .thmDecl
      { name := `_taintedEvidence, levelParams := [], type := fact,
        value := mkConst `_taintedAxiom }
  logInfo "this report must not survive"

-- A tactic proof through a local definition whose value uses a fresh axiom: the proof term
-- mentions only the local, the kernel-checked closure substitutes it, and `closeGoal` audits
-- that closure too.
open Lean Elab Tactic Meta in
/-- info: refused: closeGoal: the proof depends on [_letAxiom (through -/
#guard_msgs (info, substring := true) in
run_elab withoutModifyingEnv do
  let fact ← mkEq (← mkAppM ``HAdd.hAdd #[mkNatLit 3, mkNatLit 3]) (mkNatLit 6)
  addDecl <| .axiomDecl
    { name := `_letAxiom, levelParams := [], type := fact, isUnsafe := false }
  withLetDecl `h fact (mkConst `_letAxiom) fun h ↦ do
    let goal ← mkFreshExprMVar fact
    try
      discard <| Tactic.run goal.mvarId! <|
        CASOracle.Accept.closeGoal "closeGoal" fun copy ↦ copy.assign h
      logInfo "accepted"
    catch error =>
      logInfo m!"refused: {← error.toMessageData.toString}"

/-! ## A right basis with a zero element

The Python lists the zero polynomial between `x` and `y` in its basis for `x, y`. The answer is
accepted, and the zero is kept in the basis and in both theorems. -/

/--
info: #cas [groebner x, y, oracle := sympy]
Domain: ℚ[x, y] as MvPolynomial (Fin 2) ℚ, with x = X 0, y = X 1
Input (polynomials): x, y
Output (Gröbner basis of the same ideal (checked)): x, 0, y

[CAS.Command.details] More details
  [CAS.Command.computation] Oracle hints from sympy (not checked)
    the basis is the reduced one for the lexicographic order x > y, each element scaled to coprime
    integer coefficients with a positive leading coefficient
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] The proposed basis spans the same ideal
        Proposition: Ideal.span {X 0, X 1} = Ideal.span {X 0, 0, X 1}
        Validation: proof term checked by the kernel against this proposition
      [CAS.explanation.checkedStep] The proposed basis is a Gröbner basis
        Proposition: ∀ p ∈ Ideal.span {X 0, 0, X 1}, p ≠ 0 →
          ∃ g ∈ {X 0, 0, X 1}, MonomialOrder.lex.leadingTerm g ∣ MonomialOrder.lex.leadingTerm p
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs (whitespace := lax) in
#cas [groebner x, y, oracle := sympy] [x, y]

/-! ## Replay without an oracle

The calls the tactics suggest close their goals with no oracle at all (here the oracle is the
wrong one). The two right sums of squares are pinned with their scripts in full, exactly as they
were suggested, parsed and run, and the scripts are pasted as proofs. The reports of the command
are pinned in full, with the `example` they print or with the `none` line that says which check
failed. -/

example : ∫ x in (0 : ℝ)..1, x * Real.exp x = 1 := by
  cas [integrate primitive := fun x => (-1 + x) * Real.exp x]

example (x y : ℝ) (h1 : x * y = 1) (h2 : x = y) : x ^ 2 = 1 := by
  linear_combination h1 + x * h2

example (x y : ℝ) : 0 ≤ x ^ 4 + y ^ 4 - 4 * x * y + 2 := by
  rw [show x ^ 4 + y ^ 4 - 4 * x * y + 2 = (x ^ 2 - y ^ 2) ^ 2 + 2 * (x * y - 1) ^ 2 by ring]
  positivity

-- `x ^ 2 - 1 = (x - 1) ^ 2 + 2 * (x - 1)`, where `1 < x` enters as `0 < x - 1`.
/--
info: Try this:
  [apply] (have h₁ := sub_pos.mpr h; rw [← sub_pos, show x ^ 2 - 1 = (x - 1) ^ 2 + 2 * (x - 1) by ring]; positivity)
-/
#guard_msgs (whitespace := exact) in
example (x : ℝ) (h : 1 < x) : 1 < x ^ 2 := by
  cas [oracle := sympy]

/-- The suggested tactic proves `1 < x ^ 2` from `1 < x` without the oracle. -/
theorem sos_replay_lt (x : ℝ) (h : 1 < x) : 1 < x ^ 2 := by
  (have h₁ := sub_pos.mpr h; rw [← sub_pos, show x ^ 2 - 1 = (x - 1) ^ 2 + 2 * (x - 1) by ring]; positivity)

-- The command prints the same script, after `intro`, in an `example` of the statement it proves,
-- checked where the command is.
/--
info: #cas [sos x, oracle := sympy]
Domain: x ∈ ℝ
Input (polynomial inequality): (1 < x → 1 < x ^ 2)
Output (sum of squares with a positive term (checked)): (x - 1) ^ 2 + 2 * (x - 1)

[CAS.Command.details] More details
  [CAS.Command.computation] Oracle-free proof
    example :
        ∀ (x : ℝ), 1 < x → 1 < x ^ 2 := by
      (intro x h₁; have h₂ := sub_pos.mpr h₁; rw [← sub_pos, show x ^ 2 - 1 = (x - 1) ^ 2 + 2 * (x - 1) by ring]; positivity)
  [CAS.Command.computation] Oracle hints from sympy (not checked)
    the Gram matrix was found numerically by cvxpy and rounded to exact rationals
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Sum of squares
        Proposition: ∀ (x : ℝ), 1 < x → 1 < x ^ 2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs (whitespace := exact) in
#cas [sos x, oracle := sympy] (1 < x → 1 < x ^ 2)

/-- The command's suggested script proves `1 < x ^ 2` for every real `x > 1`. -/
theorem sos_replay_command :
    ∀ (x : ℝ), 1 < x → 1 < x ^ 2 := by
  (intro x h₁; have h₂ := sub_pos.mpr h₁; rw [← sub_pos, show x ^ 2 - 1 = (x - 1) ^ 2 + 2 * (x - 1) by ring]; positivity)

section
open Real
variable (sin : ℝ → ℝ)

-- Here `sin` is the variable of the section, so the report names `Real.sin`, and the `example`
-- is checked in this section.
/--
info: #cas [sos x, oracle := sympy]
Domain: x ∈ ℝ
Input (polynomial inequality): (0 ≤ (Real.sin x) ^ 2)
Output (sum of squares (checked)): Real.sin x ^ 2

[CAS.Command.details] More details
  [CAS.Command.computation] Oracle-free proof
    example :
        ∀ (x : ℝ), 0 ≤ Real.sin x ^ 2 := by
      (intro x; rw [show Real.sin x ^ 2 = Real.sin x ^ 2 by ring]; positivity)
  [CAS.Command.computation] Oracle hints from sympy (not checked)
    the Gram matrix was found numerically by cvxpy and rounded to exact rationals
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Sum of squares
        Proposition: ∀ (x : ℝ), 0 ≤ Real.sin x ^ 2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs (whitespace := exact) in
#cas [sos x, oracle := sympy] (0 ≤ (Real.sin x) ^ 2)

/-- The command's script proves `0 ≤ Real.sin x ^ 2` for every real `x`, with a variable `sin`. -/
theorem sos_replay_section :
    ∀ (x : ℝ), 0 ≤ Real.sin x ^ 2 := by
  (intro x; rw [show Real.sin x ^ 2 = Real.sin x ^ 2 by ring]; positivity)

end

section
variable [LE ℝ]

-- The script proves the statement with the order of `ℝ`, but in this section `0 ≤ x ^ 2` is read
-- with the order of the variable, so the `example` would state another proposition.
/--
info: #cas [sos x, oracle := sympy]
Domain: x ∈ ℝ
Input (polynomial): (x ^ 2)
Output (sum of squares (checked)): x ^ 2

[CAS.Command.details] More details
  [CAS.Command.computation] Oracle-free proof
    none: the script checks on the goal, but where the command is, the `example` with it does not state the proposition proved
  [CAS.Command.computation] Oracle hints from sympy (not checked)
    the Gram matrix was found numerically by cvxpy and rounded to exact rationals
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Sum of squares
        Proposition: ∀ (x : ℝ), 0 ≤ x ^ 2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs (whitespace := exact) in
#cas [sos x, oracle := sympy] (x ^ 2)

end

-- The atom `(⌊x⌋ : ℝ)` prints as `↑⌊x⌋`, which does not say to which type it is cast, so the
-- script as printed does not check on the goal, and the statement is proved from the certificate
-- over the atom as elaborated.
/--
info: #cas [sos x, oracle := sympy]
Domain: x ∈ ℝ
Input (polynomial): ((⌊x⌋ : ℝ) ^ 2)
Output (sum of squares (checked)): ↑⌊x⌋ ^ 2

[CAS.Command.details] More details
  [CAS.Command.computation] Oracle-free proof
    none: the script as printed does not check here; the statement is proved from the same certificate over the atoms as elaborated
  [CAS.Command.computation] Oracle hints from sympy (not checked)
    the Gram matrix was found numerically by cvxpy and rounded to exact rationals
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Sum of squares
        Proposition: ∀ (x : ℝ), 0 ≤ ↑⌊x⌋ ^ 2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs (whitespace := exact) in
#cas [sos x, oracle := sympy] ((⌊x⌋ : ℝ) ^ 2)

noncomputable opaque sos_atom : ℝ := 0

section
variable (h : 0 < sos_atom ^ 2)

-- The statement does not use the variable, hence the name `_x`. The search does not use `h`. In
-- the `example` with the script, `positivity` proves `0 ≤ sos_atom ^ 2` from `h`, so the
-- `example` command takes `h` as an argument, and the declaration is not the proposition proved.
/--
info: #cas [sos _x, oracle := sympy]
Domain: _x ∈ ℝ
Input (polynomial inequality): (0 ≤ sos_atom ^ 2)
Output (sum of squares (checked)): sos_atom ^ 2

[CAS.Command.details] More details
  [CAS.Command.computation] Oracle-free proof
    none: the script checks on the goal, but where the command is, the declaration of the `example` with it is not the proposition proved
  [CAS.Command.computation] Oracle hints from sympy (not checked)
    the Gram matrix was found numerically by cvxpy and rounded to exact rationals
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Sum of squares
        Proposition: ∀ (_x : ℝ), 0 ≤ sos_atom ^ 2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs (whitespace := exact) in
#cas [sos _x, oracle := sympy] (0 ≤ sos_atom ^ 2)

-- Like an `example`, a `def` takes the variables of the section that its proof uses (a `theorem`
-- takes those of its statement), so the type of this one shows the hypothesis that the `example`
-- with the script takes.
set_option linter.defProp false in
/-- The replay of the script: `0 ≤ sos_atom ^ 2` for every real `_x`, from the section's `h`. -/
def sos_replay_hypothesis :
    ∀ (_x : ℝ), 0 ≤ sos_atom ^ 2 := by
  (intro _x; rw [show sos_atom ^ 2 = sos_atom ^ 2 by ring]; positivity)

/-- info: sos_replay_hypothesis (h : 0 < sos_atom ^ 2) (_x : ℝ) : 0 ≤ sos_atom ^ 2 -/
#guard_msgs (whitespace := exact) in
#check sos_replay_hypothesis

end

-- The Python answers with the premise `0 < x` as the multiplier, though `x + 1` needs none:
-- `x * (x + 1) = x ^ 2 + x`, and `0 ≤ x` rests on the premise.
/--
info: Try this:
  [apply] (intro x h₁; refine pos_of_mul_pos_right (a := x) ?_ (by positivity); rw [show x * (x + 1) = x ^ 2 + x by ring]; positivity)
-/
#guard_msgs (whitespace := exact) in
example : ∀ x : ℝ, 0 < x → 0 < x + 1 := by
  cas [oracle := sympy]

/-- The replay proves `0 < x + 1` for positive `x` by using `x` as a multiplier. -/
theorem sos_replay_multiplier : ∀ x : ℝ, 0 < x → 0 < x + 1 := by
  (intro x h₁; refine pos_of_mul_pos_right (a := x) ?_ (by positivity); rw [show x * (x + 1) = x ^ 2 + x by ring]; positivity)

/-- info: 'sos_replay_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := exact) in
#print axioms sos_replay_lt

/-- info: 'sos_replay_multiplier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := exact) in
#print axioms sos_replay_multiplier

/-- info: 'sos_replay_command' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := exact) in
#print axioms sos_replay_command

/-- info: 'sos_replay_section' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := exact) in
#print axioms sos_replay_section

/-- info: 'sos_replay_hypothesis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := exact) in
#print axioms sos_replay_hypothesis

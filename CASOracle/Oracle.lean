/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

import Lean.Elab.Command
import DSLean.Process
import CAS.IncludeStr

/-!
# The oracles and how they run

The commands of `CASOracle` ask an external program for a proposal (a primitive, a
factorization, cofactors, a root, a value) and then prove it in Lean, or refuse. The programs
are SymPy, SageMath, PARI/GP, FLINT, Maxima, Giac, Singular and Gappa, the constructors of
`Oracle`, which `Oracle.all` lists, and `Oracle.tasks` lists the tasks each one takes. `run` runs
the program of an oracle for one request and returns its answer; nothing it returns is trusted.

## Implementation notes

The oracles are built on DSLean, used as a Lake package: DSLean's grammars (`CASOracle.Syntax`)
write the request and read the answer, and DSLean's runner (`DSLean.Process`) runs the program
for one request, with the deadline `cas.oracle.timeout` (milliseconds), a bound on its output,
the elaborator's cancellation, and on every exit path an attempt to end its process group:
`SIGTERM`, then `SIGKILL` through the system `kill` when there is one, with bounded waits of
about five seconds in all (a descendant that leaves the group, or a process in an
uninterruptible wait, is not covered). It opens no socket and starts no server. CASOracle copies
none of DSLean's code. The revision we pin is DSLean's port to Lean 4.36.0, the tag `v4.36.0` of
<https://github.com/Robertboy18/DSLean>, with five changes: operand precedences that follow the
precedence option, pattern priorities that hold in `toExternal'`, a runner with a deadline and a
bounded output (`DSLean/Process.lean`), Gappa's input grammar in a module of its own, and info
trees turned off while the `gappa` tactic elaborates the proof it generates. The files of
`CASOracle` are ordinary files, not `module`s, because DSLean's are, so a `module` file cannot
import them.

The program of each oracle comes from an environment variable:

* `sympy`, `pari`, `flint`: the Python of `SYMLEAN_SYMPY_PYTHON`, `SYMLEAN_PARI_PYTHON` or
  `SYMLEAN_FLINT_PYTHON`, else of `SYMLEAN_ORACLE_PYTHON`, else `python3`, run as
  `python -c <program>`; it needs SymPy, and `cypari2` or `python-flint` for PARI and FLINT;
* `sage`: `SYMLEAN_SAGE_PATH` (default `sage`), run as `sage -c <program>`;
* `maxima`: `SYMLEAN_MAXIMA_PATH` (default `maxima`), as `maxima --very-quiet --batch-string`;
* `giac`: `SYMLEAN_GIAC_PATH` (default `giac`), with the script on standard input. The program
  inherits the environment. With neither `OPENBLAS_NUM_THREADS` nor `OMP_NUM_THREADS` in it,
  Giac's linear algebra library starts one thread per core. Without `XCAS_ROOT`
  Giac looks for its help index in `doc/local/` of the working directory and, if that directory
  exists, creates or empties three files in it;
* `singular`: `SYMLEAN_SINGULAR_PATH` (default `Singular`), as
  `Singular -q --no-rc --no-warn --cpus=1` with the script on standard input;
* `gappa`: `SYMLEAN_GAPPA_PATH` (default `gappa`), with the problem on standard input.

The Python programs are `oracle/symlean_oracle.py`, embedded here with `include_str`, followed
by one call (`askPython`). Maxima, Giac and Singular are batch programs: each runs a script of
`Script` written for the task, with the arguments of `Oracle.program?` (`askProgram`). Giac reads
its script as a session on standard input and writes with `print` on its standard error, where
its records are read; its standard output holds the echo of the session. A Giac script prints
the value of one command and has no loop, test or variable of its own; Lean
splits the lists that Giac prints (`Translate.listItems?`). Singular reads its script on standard
input. After an error it writes a message on its standard output, goes on with the next
statement and exits with code 0. So a Singular script is the procedures of
`oracle/symlean_oracle.sing`, embedded here as well, and one call of them inside a procedure:
an error leaves the procedures, and each prints its records at its end, all of them or none
(`Script.singular`). A program answers with lines
`@@ key payload`; other lines are ignored. A record `@@ unavailable reason`,
`@@ unsupported reason` or `@@ failed reason` makes the run that failure; a record whose key the
task does not expect, an exit code other than 0, or no record at all (except for the tasks whose
answer is a list, which may be empty) is refused. Each command then checks how many records of
each key it reads, and `groebner` also their order. Numbers in records are read with bounds on
their length before their value is computed.

Gappa, which only the task `enclose` asks, is cited in `CASOracle.Numeric`, and the solvers
behind the sums of squares in `CASOracle.Sos`. The versions named below and there are those of
a run of `tests/oracle/run.sh` on Linux x86-64.

## References

* taterowney, *DSLean: A Bi-directional Interface Between Lean 4 and External Languages*,
  <https://github.com/taterowney/DSLean>, licensed under CC BY 4.0,
  <https://creativecommons.org/licenses/by/4.0/>. `lake-manifest.json` pins the revision we use.
* Aaron Meurer, Christopher P. Smith, Mateusz Paprocki, Ondřej Čertík, Sergey B. Kirpichev,
  Matthew Rocklin, AMiT Kumar, Sergiu Ivanov, Jason K. Moore, Sartaj Singh, Thilina Rathnayake,
  Sean Vig, Brian E. Granger, Richard P. Muller, Francesco Bonazzi, Harsh Gupta, Shivam Vats,
  Fredrik Johansson, Fabian Pedregosa, Matthew J. Curry, Andy R. Terrel, Štěpán Roučka,
  Ashutosh Saboo, Isuru Fernando, Sumith Kulal, Robert Cimrman and Anthony Scopatz, "SymPy:
  symbolic computing in Python", *PeerJ Computer Science* 3 (2017), e103,
  <https://doi.org/10.7717/peerj-cs.103>. Tested with version 1.14.0.
* The Sage Developers, *SageMath, the Sage Mathematics Software System*,
  <https://www.sagemath.org>, <https://doi.org/10.5281/zenodo.8042260>. Tested with version 10.10.
* Wolfram Decker, Gert-Martin Greuel, Gerhard Pfister and Hans Schönemann, *Singular: A computer
  algebra system for polynomial computations*, <https://www.singular.uni-kl.de>. Tested with
  version 4.4.1, both for the `singular` oracle, which runs Singular itself (the conda-forge
  build 4.4.1.5), and inside SageMath 10.10, which computes with it the Gröbner bases, cofactors
  and factorizations of the `sage` oracle.
* The PARI Group, *PARI/GP*, Univ. Bordeaux, <https://pari.math.u-bordeaux.fr/>. Tested with
  version 2.17.4, through cypari2 2.2.4.
* The FLINT team, *FLINT: Fast Library for Number Theory*, 2026, <https://flintlib.org>. Tested
  with version 3.5.0, through python-flint 0.9.0.
* Fredrik Johansson, "Arb: Efficient Arbitrary-Precision Midpoint-Radius Interval Arithmetic",
  *IEEE Transactions on Computers* 66 (2017), pp. 1281-1292,
  <https://doi.org/10.1109/TC.2017.2690633>, the ball arithmetic of the `flint` oracle.
* Maxima.sourceforge.io, *Maxima, a Computer Algebra System*, <https://maxima.sourceforge.io/>.
  Tested with version 5.50.0.
* Bernard Parisse and Renée De Graeve, *Giac/Xcas*,
  <https://www-fourier.univ-grenoble-alpes.fr/~parisse/giac.html>. Tested with version 2.0.0
  (the conda-forge build 2.0.0.19).
-/

namespace CASOracle

open Lean

/-- The external systems SymLean can consult. -/
inductive Oracle where
  | sympy
  | sage
  | pari
  | flint
  | maxima
  | giac
  | singular
  | gappa
  deriving BEq, Inhabited, Repr

namespace Oracle

/-- Every oracle, in the order in which messages list them. -/
def all : List Oracle := [.sympy, .sage, .pari, .flint, .maxima, .giac, .singular, .gappa]

example : ∀ oracle : Oracle, oracle ∈ all := by
  intro oracle
  cases oracle <;> simp [all]

/-- The name of the oracle in reports, which is also the identifier that names it in the command
syntax. -/
def name : Oracle → String
  | .sympy => "sympy"
  | .sage => "sage"
  | .pari => "pari"
  | .flint => "flint"
  | .maxima => "maxima"
  | .giac => "giac"
  | .singular => "singular"
  | .gappa => "gappa"

/-- The oracle named by an identifier of the command syntax: the one of `all` with that name. -/
def ofName? (identifier : Name) : Option Oracle :=
  all.find? fun oracle ↦ identifier == Name.mkSimple oracle.name

/-- The names of all oracles, for messages: `sympy, sage, pari, flint, maxima, giac, singular or
gappa`. -/
def choices : String :=
  let names := all.map name
  ", ".intercalate names.dropLast ++ " or " ++ names.getLastD ""

/-- The environment variable that names the oracle's program. -/
def programVariable : Oracle → String
  | .sympy => "SYMLEAN_SYMPY_PYTHON"
  | .sage => "SYMLEAN_SAGE_PATH"
  | .pari => "SYMLEAN_PARI_PYTHON"
  | .flint => "SYMLEAN_FLINT_PYTHON"
  | .maxima => "SYMLEAN_MAXIMA_PATH"
  | .giac => "SYMLEAN_GIAC_PATH"
  | .singular => "SYMLEAN_SINGULAR_PATH"
  | .gappa => "SYMLEAN_GAPPA_PATH"

/-- Whether the oracle runs in Python. -/
def isPython : Oracle → Bool
  | .sympy | .pari | .flint => true
  | .sage | .maxima | .giac | .singular | .gappa => false

/-- The variables the oracle's program may come from, for messages. -/
def configuration (oracle : Oracle) : String :=
  if oracle.isPython then s!"{oracle.programVariable} or SYMLEAN_ORACLE_PYTHON"
  else oracle.programVariable

/-- The DSLean tool that runs the oracle: the program of its variable, else, for the Python
backends, the Python of `SYMLEAN_ORACLE_PYTHON`, else the program's usual name. -/
def tool (oracle : Oracle) : IO DSLean.ExternalTool := do
  let default ← match oracle with
    | .sympy | .pari | .flint => pure ((← IO.getEnv "SYMLEAN_ORACLE_PYTHON").getD "python3")
    | .sage => pure "sage"
    | .maxima => pure "maxima"
    | .giac => pure "giac"
    | .singular => pure "Singular"
    | .gappa => pure "gappa"
  return { name := oracle.name, envVar := oracle.programVariable, default }

end Oracle

/-- The deadline of one external oracle run, in milliseconds. -/
register_option cas.oracle.timeout : Nat := {
  defValue := 120000
  descr := "deadline of one external oracle run of CASOracle, in milliseconds"
}

/-- The Python programs, embedded at build time. -/
def pythonProgram : String := include_str "../oracle/symlean_oracle.py"

/-- Why an oracle gave no answer. -/
inductive Failure where
  /-- The program could not be started, or lacks the package the backend needs. -/
  | unavailable (reason : String)
  /-- The backend has no answer in the checked language, or no such task. -/
  | unsupported (reason : String)
  /-- The program ran past the deadline and was ended. -/
  | timeout (milliseconds : Nat)
  /-- The program failed, or its output is not an answer. -/
  | failed (reason : String)

/-- A one-line account of a failure. -/
def Failure.render (oracle : Oracle) : Failure → String
  | .unavailable reason => s!"oracle {oracle.name} is unavailable: {reason} (configure it with \
      {oracle.configuration})"
  | .unsupported reason => s!"oracle {oracle.name} has no checkable answer: {reason}"
  | .timeout ms => s!"oracle {oracle.name} did not answer within {ms} ms \
      (option cas.oracle.timeout)"
  | .failed reason => s!"oracle {oracle.name} failed: {reason}"

/-- Fail with `failure`. -/
def fail {α : Type} (oracle : Oracle) (failure : Failure) : CoreM α :=
  throwError (failure.render oracle)

/-- At most the last `n` characters of `text`. -/
private def lastChars (text : String) (n : Nat) : String :=
  if text.length > n then (text.drop (text.length - n)).toString else text

/-- Run the oracle's program with `args` and `stdin` under `cas.oracle.timeout` and the
elaborator's cancellation (which interrupts the elaboration, as any cancellation does). -/
def run (oracle : Oracle) (args : Array String) (stdin : String := "")
    (maxErrorBytes : Nat := 4096) : CoreM DSLean.RunResult := do
  let timeoutMs := cas.oracle.timeout.get (← getOptions)
  let tool ← (oracle.tool : IO _)
  match ← (tool.run args stdin { timeoutMs, maxErrorBytes } (← read).cancelTk? : IO _) with
  | .ok result => return result
  | .error .cancelled => throwInterruptException
  | .error (.unavailable reason) => fail oracle (.unavailable reason)
  | .error (.timeout ms) => fail oracle (.timeout ms)
  | .error (.overflow bytes) => fail oracle (.failed s!"the answer is over {bytes} bytes")
  | .error .notUTF8 => fail oracle (.failed "the standard output is not UTF-8")
  | .error .unclosed => fail oracle (.failed "the standard output did not close")
  | .error (.io error) => fail oracle (.failed error)

/-- One answer record `@@ key payload`. -/
structure Record where
  /-- The record's key. -/
  key : String
  /-- The rest of the line. -/
  payload : String
  deriving Inhabited

/-- The records of a run, with `keys` the keys the task expects; `allowEmpty` for a task whose
answer is a list, which may be empty; `onStderr` for a program that writes its records on its
standard error, whose standard output is then read only for the message of a run without an
answer. -/
def records (oracle : Oracle) (keys : List String) (result : DSLean.RunResult)
    (allowEmpty : Bool := false) (onStderr : Bool := false) : CoreM (Array Record) := do
  let output := if onStderr then result.stderr else result.stdout
  let found := (output.splitOn "\n").toArray.filterMap fun line ↦ do
    let line := line.trimAscii.toString
    guard (line.startsWith "@@ ")
    let key :: rest := ((line.drop 3).toString.splitOn " ") | none
    return { key, payload := (" ".intercalate rest).trimAscii.toString }
  for record in found do
    match record.key with
    | "unavailable" => fail oracle (.unavailable record.payload)
    | "unsupported" => fail oracle (.unsupported record.payload)
    | "failed" => fail oracle (.failed record.payload)
    | key => unless keys.contains key do
        fail oracle (.failed s!"the answer has an unexpected record {key}")
  if found.isEmpty && !(allowEmpty && result.exitCode == 0) then
    -- A program with its records on standard error writes its messages on both streams. The
    -- runner hands over a standard error that is not UTF-8 as the empty text.
    let detail := if onStderr then
        s!"{lastChars result.stdout 300}\n{if result.stderr.isEmpty then
          "(the standard error is empty or is not UTF-8)" else lastChars result.stderr 300}"
      else lastChars (if result.stderr.isEmpty then result.stdout else result.stderr) 600
    if result.exitCode == 127 then
      fail oracle (.unavailable s!"the program did not run: {detail}")
    fail oracle (.failed s!"exit code {result.exitCode}, no answer: {detail}")
  unless result.exitCode == 0 do
    fail oracle (.failed s!"the oracle exited with code {result.exitCode} after answering")
  return found

/-- The payloads of the records with `key`, at most `max` of them. -/
def payloads (oracle : Oracle) (found : Array Record) (key : String) (max : Nat) :
    CoreM (Array String) := do
  let selected := (found.filter (·.key == key)).map (·.payload)
  if selected.size > max then
    fail oracle (.failed s!"the answer has {selected.size} records {key}, over {max}")
  return selected

/-- The payload of the one record with `key`. -/
def payload (oracle : Oracle) (found : Array Record) (key : String) : CoreM String := do
  match (found.filter (·.key == key)).toList with
  | [record] => return record.payload
  | [] => fail oracle (.failed s!"the answer has no record {key}")
  | _ => fail oracle (.failed s!"the answer has several records {key}")

/-- A Python string literal of `text`. -/
def py (text : String) : String :=
  "\"" ++ String.join (text.toList.map fun c ↦
    if c == '\\' then "\\\\" else if c == '"' then "\\\"" else if c == '\n' then "\\n"
    else c.toString) ++ "\""

/-- A Python list of string literals. -/
def pyList (items : List String) : String := "[" ++ ", ".intercalate (items.map py) ++ "]"

/-- The Python expression reading the request text `text` over the variables `names`. -/
def pyRead (text : String) (names : List String) : String :=
  s!"read({py text}, {pyList names})"

/-- The Python expression of the SymPy variables `names`. -/
def pyVariables (names : List String) : String :=
  "V(" ++ ", ".intercalate (names.map py) ++ ")"

/-- The tasks of each oracle. The task `sos` of `sympy` needs cvxpy (`pip install cvxpy`) in the
oracle's Python. -/
def Oracle.tasks : Oracle → List String
  | .sympy => ["integrate", "factor", "solve", "nroots", "nintegrate", "eigenvalues", "groebner",
      "member", "dsolve", "sum", "sos"]
  | .sage => ["integrate", "factor", "solve", "nintegrate", "eigenvalues", "groebner", "member",
      "dsolve", "sum"]
  | .pari | .flint => ["factor", "nroots", "nintegrate", "eigenvalues"]
  | .maxima => ["integrate", "factor"]
  | .giac => ["integrate", "solve", "dsolve", "sum"]
  | .singular => ["factor", "groebner", "member"]
  | .gappa => ["enclose"]

/-- Refuse a task the oracle does not have. -/
def requireTask (oracle : Oracle) (task : String) : CoreM Unit := do
  unless oracle.tasks.contains task do fail oracle (.unsupported s!"{oracle.name} has no {task}")

/-- The class of `oracle/symlean_oracle.py` that answers the oracle's tasks (`askPython`): the
Python backends and Sage have one. -/
def Oracle.backend? : Oracle → Option String
  | .sympy => some "SympyBackend"
  | .sage => some "SageBackend"
  | .pari => some "PariBackend"
  | .flint => some "FlintBackend"
  | .maxima | .giac | .singular | .gappa => none

/-- Run the method `task` of the oracle's backend in `oracle/symlean_oracle.py` on the Python
`arguments`, and return its records, `keys` being the keys the task prints. -/
def askPython (oracle : Oracle) (task : String) (keys : List String) (arguments : String)
    (allowEmpty : Bool := false) : CoreM (Array Record) := do
  requireTask oracle task
  let some backend := oracle.backend?
    | fail oracle (.unsupported s!"{oracle.name} does not run in Python")
  let source := pythonProgram ++ s!"\nrun(lambda: {backend}().{task}({arguments}))\n"
  records oracle keys (← run oracle #["-c", source]) allowEmpty

/-- How a batch program runs a script: it is given `arguments` and then the script as its last
argument, or the script on its standard input when `stdin` is set. It writes its records on its
standard output, or on its standard error when `recordsOnStderr` is set. -/
structure Program where
  /-- The arguments before the script. -/
  arguments : Array String
  /-- Whether the script goes on standard input instead of being the last argument. -/
  stdin : Bool := false
  /-- Whether the records are on standard error instead of standard output. -/
  recordsOnStderr : Bool := false

/-- The batch program of an oracle whose tasks run as scripts of `Script` (`askProgram`). The
Python backends and Sage run `oracle/symlean_oracle.py` instead (`askPython`), and Gappa reads a
problem in its own language and writes no records (`CASOracle.Numeric`). -/
def Oracle.program? : Oracle → Option Program
  | .maxima => some { arguments := #["--very-quiet", "--batch-string"] }
  | .giac => some { arguments := #[], stdin := true, recordsOnStderr := true }
  | .singular => some { arguments := #["-q", "--no-rc", "--no-warn", "--cpus=1"], stdin := true }
  | .sympy | .sage | .pari | .flint | .gappa => none

/-- Run `script`, a script of the task `task`, on the oracle's batch program (`Oracle.program?`)
and return its records, `keys` being the keys the task prints; a run without a record is
refused. A standard error that holds the records is kept up to the bound of the standard output,
and a longer one is refused. -/
def askProgram (oracle : Oracle) (task : String) (keys : List String) (script : String) :
    CoreM (Array Record) := do
  requireTask oracle task
  let some program := oracle.program?
    | fail oracle (.unsupported s!"{oracle.name} runs no scripts")
  let arguments := if program.stdin then program.arguments else program.arguments.push script
  let stdin := if program.stdin then script else ""
  let bound := ({} : DSLean.RunLimits).maxOutputBytes
  let result ← if program.recordsOnStderr then run oracle arguments stdin (maxErrorBytes := bound)
    else run oracle arguments stdin
  if program.recordsOnStderr && result.stderrTruncated then
    fail oracle (.failed s!"the answer is over {bound} bytes")
  records oracle keys result (onStderr := program.recordsOnStderr)

namespace Script

/-- The Maxima script that prints the value of the expression `command` as Maxima's `string`
writes it, on one line, under the record `key`. Maxima echoes its batch input, whose lines begin
with `print(`, not with `@@`. -/
def maxima (key command : String) : String :=
  s!"display2d:false$ linel:1000000$ print(\"@@\", \"{key}\", string({command}))$"

/-- The first line of every Giac script: Giac's own syntax rather than Maple's, real numbers,
exact arithmetic, angles in radians, and one thread for Giac's own computations. -/
def giacSettings : String :=
  "maple_mode(0):; complex_mode:=0:; approx_mode:=0:; angle_radian:=1:; threads:=1:;"

/-- The Giac script that prints the value of the expression `command` as Giac's `string` writes
it, on one line, under the record `key`. Giac's `print` writes on standard error. A command that
stops with an error prints no record, and Giac writes its message on either stream. -/
def giac (key command : String) : String :=
  s!"{giacSettings}\nprint(\"@@ {key} \"+string({command})):;\n"

/-- The script that prints the value of an expression under a record, for the batch programs
that evaluate expressions (`maxima`, `giac`); `none` for the other oracles. -/
def value? : Oracle → Option (String → String → String)
  | .maxima => some maxima
  | .giac => some giac
  | .sympy | .sage | .pari | .flint | .singular | .gappa => none

/-- The procedures of the `singular` oracle, embedded at build time: one for each of its tasks,
which prints the records of the task once all of them are computed. -/
def singularProcedures : String := include_str "../oracle/symlean_oracle.sing"

/-- The Singular script that runs the statements `body` in `ℚ[v0, v1, …]` with `variables`
variables (one when there is none) and the lexicographic order `v0 > v1 > …`, after the
procedures of `oracle/symlean_oracle.sing`; the statements define the polynomials of a request
and call the procedure of its task. They run inside a procedure, which an error leaves, so a
script prints all the records of its task or none. Polynomials are printed with `*` and `^`
(`short = 0`), and bases are reduced (`redSB`, `redTail`). -/
def singular (variables : Nat) (body : List String) : String :=
  let names := ", ".intercalate ((List.range (max variables 1)).map (s!"v{·}"))
  "\n".intercalate
    ([s!"ring symleanR = 0, ({names}), lp;", "short = 0;", "option(redSB);", "option(redTail);",
      singularProcedures.trimAscii.toString, "proc symleanAnswer()", "{"] ++
    body.map ("  " ++ ·) ++ ["}", "symleanAnswer();", "quit;"]) ++ "\n"

end Script

end CASOracle

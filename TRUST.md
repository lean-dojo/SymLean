# What a SymLean proof trusts

The default SymLean build checks its theorems in Lean's kernel. Run `bash scripts/audit.sh` to check
axiom dependencies and list compiler hooks in the built library. Use `--inventory` for reporting
only, or pass `CASOracle` to audit that optional library after building it.

## Always

- Lean 4.36.0's kernel and the axioms `propext`, `Classical.choice` and `Quot.sound`. The audit fails
  on any other axiom dependency, with a single exception for `lcProof` in the unsafe implementation
  `CAS.Numerics.natCompactImpl` itself.
- Mathlib v4.36.0: the statements use its definitions (`Real.arctan`, the interval and
  Bochner integrals, `IntegrableOn`, `HasSum`, `tsum`), so they mean what those definitions mean.
- The SymLean definitions that appear in printed statements: `CAS.erf` (the definition of Mathlib
  pull request #34053), `CAS.Analysis.SpecialFunctions.legendre`, `CAS.AlgRoot.real` and
  `CAS.AlgRoot.complex` (`Classical.epsilon` choices, meaningful under `real_spec` and
  `complex_spec`), `coeffEval` and `polyC` (Mathlib's `Polynomial.ofCoeffList` mapped to `ℂ`), the
  relations `EnclosedOn`, `BoundOn`, `ApproxOn` and `ResidualBound` of
  `CAS/Certificate/Relations.lean`, `CAS.Exact.exprFn` with `CAS.Verified.Expr` and its evaluation,
  and the rational boxes: a reader must read them to know what an answer states.
- Embedded inputs: a theorem proved from `include_str` or `json_data%` is about the file's content
  when the module was built, and the `SymLean.embeddedInputs` facet makes Lake rebuild when the file
  changes, within the exclusions documented in `CAS/IncludeStr.lean`. `pinned_hex%` also compares
  the length and the SHA-256 digest of its text with the numbers written in the module, with compiled
  code while the module is elaborated; the comparison names the text and proves nothing, and the
  literals it stores are data that the kernel reads. It reads the lines of the text with
  `hexEntry?`, the function with which a run reads its files, and refuses a text with a line
  that is not in the format.
- Lake's rebuild rule: a module-system importer is not rebuilt when only the compiled code of an
  imported tactic changes, so a `#guard_msgs` that pins tactic output can replay a stale message until
  that module is rebuilt.

## Only in the fast profile

- `set_option cega.nativeCertificates true` or `lake build -R -Kcertificates=fast` lets `cega [fast]`
  and `cega [fast, batch := n]` (`CAS.Numerics.Tactic`)
  check finite certificates with compiled code through Lean's `nativeEqTrue`, which runs the
  compiled test and adds an axiom that states its result; this trusts Lean's compiler and runtime,
  and the theorem shows it in its axioms (`…._native.cegaFast.ax_*`, `tests/cega/Readme.lean`).
  Off by default.
- Under the same option `cert_eval` evaluates the tests of the certificate framework with compiled
  code, and with it `cert_shard`, `cert_cond`, `cert_scalar`, `cert_decide` and `cert_reduce`; each
  loop that compiled code evaluates adds one such axiom (`tests/cert/Native.lean`). A statement
  that the kernel has already proved within the same proof may be reused, and then adds none. The
  build runs compiled code in Lean's interpreter, since the library is not compiled to machine code.
- A native test that reads a literal of `2 ^ 4096` or more, such as a block of a table that
  `pinned_hex%` stores, reads it through SymLean's unsafe `CAS.Numerics.natCompactImpl`, which
  takes the value from the definition of the literal in the environment. The axiom of such a test
  therefore also trusts that function (`tests/cert/run.sh` builds one certificate of this kind in
  both profiles). The kernel reads the definition itself.

## The arithmetic of `cega`, which no statement mentions

- `cega [use_floats]`, `(arith := F)`, `set_option cega.arithmetic` and `weak.cega.arithmetic` in
  the Lean options of a lakefile choose how a box query computes its enclosure: with exact
  rational endpoints, the default, or with endpoints in the IEEE binary format `F` of FloatLib.
  The accepted goal is about real numbers in either case. Lean's kernel checks both proofs, with
  the three standard axioms (`CAS/Examples/CEGA/Floats.lean`). `CAS.CEGA.holds_of_refutes` proves
  a bound on every point of the box when the FloatLib refutation succeeds.
  `CAS.Verified.Expr.eval_toFloatLib` relates the two expression languages. That the query
  `CAS.CEGA.Check.enclose?` encloses the expression is `CAS.CEGA.Check.bounds_of_evalZero?`, from
  FloatLib's `Interval.Expr.containsReal_evalZero?`.
  In the binary endpoint backend, FloatLib computes in exact rationals and rounds each result
  outward to finite numbers of `F` (`Backend.ofRounding_sound`). No machine floating-point
  operation needs to be trusted.
- The build option sets a default that individual calls can override. Successful calls in
  either arithmetic prove the original goal. A float call that cannot prove its goal fails with
  the format and the reason, rather than switching to exact endpoints (`tests/floats/run.sh`).

## Compiled code that cannot reach a theorem

- 8 declarations with an `implemented_by` attribute, each naming an unsafe definition as its
  compiled implementation: `CAS.Numerics.evalNatTerm`, `evalRowFun`,
  `evalString` and `natCompact` (evaluate terms while Lean elaborates, or keep large literals out of
  the generated C; in the fast profile `natCompact` does reach a theorem, as said above), and
  `CAS.Tactic.RouteRegistry.evalCloser`, `evalCommandBackend`,
  `evalFactorProvider` and `evalGoalPredicate` (run registered routes): a wrong result makes a tactic
  fail or skip a route, or stores other data than the term or the file gave. The kernel still
  checks any proof, which is then a proof about the data that were stored; that these are the
  data of a file is established by the importer as it runs, not by a theorem.
- 6 `@[csimp]` lemmas, `fin_cases_eq_direct`, `fin_cons_eq_direct`, `vecCons_eq_vecConsLookup`,
  `translatedLogPanelInterval_eq_shared`, `factorRow_eq_factorRowFast` and `twoStageRow_eq_fast`,
  one per constant: kernel-proved equations that only compiled code uses, so they matter only in the
  fast profile, in `#eval` and in a run over files.
- Constructor indices `T.ctorIdx`, each implemented by the unsafe definition `T.ctorIdx._impl`
  that Lean 4.36 generates for an inductive type with several constructors and that reads the
  constructor's tag: compiled code and `#eval` trust this tag read, which no theorem relates to
  `T.ctorIdx`; the kernel uses the logical definition. `scripts/audit.sh` checks the name, the type
  and the body of each pair.
- Opaque and partial constants, from `partial def`s and their compiled copies: the kernel never
  unfolds them, so no proof depends on their code, and a theorem that mentions one knows nothing
  about its value beyond its type. `scripts/audit.sh` counts both kinds.

## A run over files, which no build contains

- `CAS.Cert.Run.Ok m family` says that there are byte strings with the lengths and SHA-256 digests
  of the manifest `m`, for the parts that some shard reads, on which the test of every shard passes.
  No module proves it for a manifest of files. A theorem that uses a run takes it as a hypothesis in
  its statement, such as `MeshSpec.cells_of_run`. Its axioms are the three standard ones, and they
  say nothing about whether the run happened. `CAS/Examples/Cert/Mesh.lean` proves the proposition
  in the kernel for seven byte strings, so it can hold.
- Whoever asserts `Run.Ok m family` after running `CAS.Cert.Run.main m family` over all shards trusts:
  - the code of `Run.exec` and `Run.main`: no theorem is about them, and that they return success
    only when every comparison and every test of `Run.ok_of_windows` passed is read from their code;
  - the program that evaluated them and `Run.shardOk`: Lean's compiler to its intermediate code and
    the interpreter of `lake env lean --run`, with the runtime and its big-number arithmetic, or a C
    compiler and linker as well for a program compiled to machine code;
  - that the `.olean` files on `LEAN_PATH` come from the sources in which the theorem was checked;
  - that the bytes which `IO.FS.readBinFile` returned are the files;
  - that the files did not change while the run lasted. A part that lies in the windows of two
    processes is read by both, and `Run.ok_of_windows` needs the same bytes in both. Equal
    digests give equal bytes only where SHA-256 has no collision, so a run that compares digests
    needs this as well;
  - the comparison of the digests. The Lean function `Sha256.hash` does it in the same program.
    With `--no-digest` another program such as `sha256sum` does it; then also that the files did
    not change in between, and that `Sha256.hash` is the function that program computes, which
    seven test vectors compare and nothing proves;
  - the script that started the processes, for the facts that every shard is in the range of some
    process and that every process returned 0;
  - that `RunMain.lean` passes the manifest and the family that the theorem names;
  - the machine, for a long run that nothing repeats.
- It does not trust:
  - any property of the family of tests, such as which entries it reads: a shard reads through a
    lookup that has no entry outside its window, and `Run.Ok.exists_texts` is proved for every family;
  - `scripts/CertStubs.lean` and `scripts/cert_synthetic.py`, which only write text that Lean checks
    or that the items above cover;
  - the collision resistance of SHA-256: the digests name the files of a run for a reader who
    repeats it. `Run.Ok.exists_texts` and `MeshSpec.cells_of_run` keep them in their conclusions,
    which are about byte strings with the lengths and digests of the manifest, and no proof draws
    anything from them. That those byte strings are the files a reader holds is where collision
    resistance would enter, outside Lean.
- The theorems of the examples that conclude `Nonempty (CellCert n)` show the pattern only: zero
  tables inhabit that type. The statements with content are `MeshSpec.cell_bound` for given
  tables, `MeshSpec.cells_of_run` for the files of a run, and `Seed.cubic_le` for a family of
  functions.

## Searches, which are trusted for nothing

- The optional `CASOracle` searches (SymPy, SageMath, FLINT, Maxima, PARI/GP, Giac, Singular and
  Gappa, through the Lean 4.36 port of DSLean) propose answers, which become theorems through
  kernel-checked proofs.
- These programs are trusted for no answer. As processes they run like any program a user
  installs: with the user's rights, in the working directory and with the environment of the Lean
  process. One side effect in the working directory is known: Giac creates or empties three files
  in `doc/local/` there if that directory exists, unless `XCAS_ROOT` names another place
 . SageMath and Maxima also keep caches, in the directories that `DOT_SAGE` and
  `MAXIMA_USERDIR` name, by default under the home directory.
- FloatLib v4.2.0: its executable arithmetic can run in compiled searches and `#eval`; the
  enclosure theorems are kernel-checked.

## Documentation

- The website compiles its ordinary examples and quotes the oracle tests.

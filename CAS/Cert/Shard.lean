/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Cert.Range
public import CAS.Cert.Table
public import CAS.Cert.Sha256
public meta import CAS.Cert.Sha256
public import CAS.Cert.HexText
public meta import CAS.Cert.HexText
public import CAS.CEGA.Elaboration
public meta import CAS.CEGA.Elaboration
public import CAS.Numerics.Json
public meta import CAS.Numerics.Json
public import CAS.Numerics.CompactLiteral
public meta import CAS.Numerics.CompactLiteral
public meta import CAS.Numerics.Binary64

/-!
# Evaluating a test, in one module or in many

## Motivation

The same test has to run in four ways: in the kernel in one declaration, in the kernel in many
modules that Lake builds in parallel, in compiled code when the build asks for it, and on data
that live in files. Can the choice be made by the build and by the size of the data alone,
without a second version of the test or of its statement?

## The idea

* `cert_eval` proves a goal `b = true` for a closed Boolean `b`. It first unfolds the
  interpreter of [Cond](Cond.lean) on the condition at hand, so that the kernel runs plain
  operations on balls instead of walking the syntax tree at every index, and then decides the
  goal with `CAS.CEGA.Elaboration.decideClosedCertificate`: in the kernel by default, with
  compiled code when the option `cega.nativeCertificates` is set (the `fast` certificate profile
  of the lakefile). The theorem then shows the axiom of native evaluation.
* `cert_shard name : t (below := N) (start := s) (count := c)` states one range of the family
  `t : ℕ → Bool`, `RangeAll (fun j : Fin N ↦ t j.val = true) s c`, and proves it by loops that
  `cert_eval` evaluates, `(batch := b)` indices in each kernel declaration. The declarations are
  elaborated one after the other, each with `Elab.async` off, so that the memory of one kernel
  evaluation is free before the next one starts.
* `cert_aggregate name : t (below := N) (shards := s, K)` joins the theorems `s0, …, s(K-1)` of
  `K` consecutive ranges into `∀ j : Fin N, t j.val = true`, in a balanced tree.
* `pinned_hex% w q n bytes "sha256" text` stores the `n` entries of `w` bits of a text, one
  entry per line ([HexText](HexText.lean)), as literals of `q` entries each, after checking the
  length and the SHA-256 digest of the text against the numbers written in the module, and
  returns the function from a block index to its literal. `nat_tree% [p0, p1, …]` is the
  function that selects one of its terms by an index: the parts of a table, or the tables of a
  certificate.

## Main results

These are commands and tactics; they prove what the kernel (or, under the option, compiled code)
accepts for the given terms. For all families and all ranges:

* `cert_eval`: a tactic for closed goals `b = true`.
* `cert_shard`, `cert_aggregate`: commands that add the range theorems and the joined theorem.
* `pinned_hex%`, `nat_tree%`: term elaborators for data.

## Relations

The ranges are those of [Range](Range.lean) and [Finite](../Numerics/Finite.lean):
`cert_shard` applies `rangeAll_of_natAll` and `rangeAll_append`, `cert_aggregate` applies
`rangeAll_append` and `forall_of_rangeAll`. The commands replace generated lists of `have`
steps; `binary_grid_shard` and `fin_cases_blocks`
([BinaryGridShards](../Numerics/BinaryGridShards.lean)) are the earlier forms for one kind of
table. `cega [batch := n]` ([Tactic](../Numerics/Tactic.lean)) cuts a family on `Fin n` into
batches and joins them by the same `rangeAll_append`, inside one proof; `cert_shard` states
the ranges as theorems, so that they can live in modules of their own. `pinned_hex%` stores
blocks as `json_slot_blocks%` does
([SlotBlocks](../Numerics/SlotBlocks.lean)), packed by `packSlotValues` and read by `blockSlot`;
its selection tree is cut into definitions of at most sixteen leaves, where `json_slot_blocks%`
builds one tree. It reads the entries of its text with `hexEntry?` ([HexText](HexText.lean)),
the function with which a run reads its files ([Run](Run.lean)), so both routes give a file the
same entries.

## Implementation notes

Each batch of `cert_shard` is checked with `set_option Elab.async false` before the next
batch starts. On tests whose kernel evaluation makes large numbers, asynchronous elaboration held
the memory of the declarations of a module together; what holds it was not traced. In the tests
measured, the memory of one declaration grew with its indices and was free after it, so the batch
size bounds what a module needs on top of what it holds before its first declaration, and it
trades against time: every declaration evaluates again what its indices share, such as the
entries of a table.

`tests/cert/build.sh` sets `MALLOC_TRIM_THRESHOLD_` and `MALLOC_TOP_PAD_`, two settings of the C
library's allocator that keep its heap from being returned to the system; the comment in the
script says why. A build through Lake inherits the two variables from the environment of the
caller.

## Scope

Lake builds modules from files, so the modules of the shards and the import list of the
aggregate are files; `scripts/CertStubs.lean` writes them from a manifest. A file read by
`pinned_hex%` is tracked by the build only when it is passed as a literal path to the string
embedding of [IncludeStr](../IncludeStr.lean). Every shard module imports the module of the
tables and so the modules of all parts; a shard that imported its own parts only would prove
its range for a window of the tables, as a shard of a run does ([Run](Run.lean)).
-/

public meta section

namespace CAS.Cert

open Lean Elab Term Meta Tactic Command CAS.Numerics

/-! ### Evaluation -/

/-- The definitions that `cert_eval` unfolds before the test is evaluated. -/
def evalUnfold : Array Name :=
  #[``Cond.run, ``Cond.check, ``CAS.Cert.ball, ``Cond.dat, ``Cond.cell, ``absE, ``maxE, ``minE,
    ``Sum.elim_inl, ``Sum.elim_inr, ``push_zero, ``push_succ, ``total, ``entryBall?, ``widen]

/--
`cert_eval`

proves a goal `b = true` for a closed Boolean `b`, by evaluation: in the kernel, or with
compiled code when `cega.nativeCertificates` is set. Before that it unfolds the interpreter of
conditions, `Cond.run`, `Cond.check` and `ball`, and the table forms `total`, `entryBall?` and
`widen`, first by `dsimp only` and then by `simp only`. `cert_eval [f, g]` also unfolds the
definitions `f` and `g`, which is needed when the condition or its data are behind definitions:
the kernel evaluates a condition that stays behind a definition by walking its syntax tree,
several times slower. A name in the list that is not a constant is an error; a definition that
the unfolding does not use is not.
-/
syntax (name := certEval) "cert_eval" (" [" ident,* "]")? : tactic

elab_rules : tactic | `(tactic| cert_eval $[[$ids,*]]?) => do
  let extra : Array Ident := match ids with
    | some ids => ids.getElems
    | none => #[]
  -- A name that is no constant is an error. Without this check it would be dropped below with
  -- the unfolding that failed on it, and the goal evaluated several times slower.
  for id in extra do
    discard <| resolveGlobalConst id
  let lemmas ← (evalUnfold.map mkCIdent ++ extra).mapM fun id ↦
    `(Lean.Parser.Tactic.simpLemma| $id:ident)
  -- Unfolding is an optimization: a goal that it does not change is evaluated as it is.
  try evalTactic (← `(tactic| dsimp only [$lemmas,*])) catch _ => pure ()
  if (← getUnsolvedGoals).isEmpty then return
  -- `dsimp` leaves a match on a numeral, such as a generator `fun j ↦ match j with | 0 => …` at
  -- `0`; `simp` rewrites it with the equations of the definition.
  try evalTactic (← `(tactic| simp only [$lemmas,*])) catch _ => pure ()
  if (← getUnsolvedGoals).isEmpty then return
  withMainContext do
    let goal ← getMainGoal
    let target ← instantiateMVars (← goal.getType)
    let proof ← CAS.CEGA.Elaboration.decideClosedCertificate target true
    unless ← isDefEq (← inferType proof) target do
      throwError "cert_eval: the checked statement does not match the goal"
    goal.assign proof
    replaceMainGoal []

/-! ### Ranges -/

/-- The ranges `(start, count)` of at most `size` indices that cut `count` indices from
`start`. -/
def batches (start count size : Nat) : Array (Nat × Nat) := Id.run do
  let mut out := #[]
  let mut done := 0
  while done < count do
    let c := min size (count - done)
    out := out.push (start + done, c)
    done := done + c
  return out

/-- The balanced join of the proofs `leaf i` of the consecutive ranges `ranges[lo], …,
ranges[hi - 1]`, each node with its range written out. -/
partial def joinRanges (ranges : Array (Nat × Nat)) (leaf : Nat → CommandElabM Term)
    (lo hi : Nat) : CommandElabM Term := do
  if hi ≤ lo + 1 then
    leaf lo
  else
    let mid := (lo + hi) / 2
    let left ← joinRanges ranges leaf lo mid
    let right ← joinRanges ranges leaf mid hi
    let start := ranges[lo]!.1
    let count := (ranges.extract lo hi).foldl (· + ·.2) 0
    `((CAS.Numerics.rangeAll_append $left $right :
      CAS.Numerics.RangeAll _ $(quote start) $(quote count)))

/--
`cert_shard name : t (below := N) (start := s) (count := c)`

adds the theorem `name : RangeAll (fun j : Fin N ↦ t j.val = true) s c` for a family
`t : ℕ → Bool`: the tests of the `c` indices from `s` pass. Each loop of `(batch := b)` indices
(by default all of them) is one declaration `name.batchK`, proved by `cert_eval` with
`Elab.async` off: the kernel evaluation of a batch ends, and its memory is free, before the
next batch starts (implementation notes).

* `(unfolding := [f, g])` passes the definitions to `cert_eval`.
* A docstring before the command becomes the docstring of `name`. Each `name.batchK` gets a
  docstring that names its range.
-/
syntax (name := certShard) (docComment)? "cert_shard " ident " : " term:max
  " (" &"below" " := " num ")" " (" &"start" " := " num ")" " (" &"count" " := " num ")"
  (atomic(" (" &"batch") " := " num ")")?
  (atomic(" (" &"unfolding") " := " "[" ident,* "]" ")")? : command

elab_rules : command
  | `($[$doc:docComment]? cert_shard $name : $t (below := $n) (start := $start)
      (count := $count) $[(batch := $batch)]? $[(unfolding := [$ids,*])]?) => do
  unless start.getNat + count.getNat ≤ n.getNat do
    throwErrorAt count "the range ends at {start.getNat + count.getNat}, after {n.getNat}"
  if let some b := batch then
    if b.getNat == 0 then throwErrorAt b "a batch holds at least one index"
  let size := match batch with
    | some b => b.getNat
    | none => max 1 count.getNat
  let ranges := batches start.getNat count.getNat size
  let extra : Array Ident := match ids with
    | some ids => ids.getElems
    | none => #[]
  let batchName (i : Nat) : Ident := mkIdent (name.getId ++ Name.mkSimple s!"batch{i}")
  -- One loop per batch, each its own declaration, elaborated and checked before the next:
  -- as asynchronous tasks the batches held the memory of their kernel evaluations together.
  for i in [0:ranges.size] do
    let (s, c) := ranges[i]!
    elabCommand (← `(command|
      set_option Elab.async false in
      theorem $(batchName i) :
          CAS.Numerics.natAll $(quote c) (fun k ↦ $t ($(quote s) + k)) = true := by
        cert_eval [$extra,*]))
    -- The generated theorem says in its docstring which range it tests.
    liftCoreM do
      addDocStringCore (← resolveGlobalConstNoOverload (batchName i))
        s!"Batch {i} of `{name.getId}`: the tests of the {c} indices from {s} pass."
  let leaf (i : Nat) : CommandElabM Term := do
    let (s, c) := ranges[i]!
    `(CAS.Cert.rangeAll_of_natAll (n := $n) (start := $(quote s)) (count := $(quote c))
        (t := $t) (by decide) $(batchName i))
  let proof ← if ranges.isEmpty then
      `(CAS.Numerics.rangeAll_zero)
    else joinRanges ranges leaf 0 ranges.size
  elabCommand (← `(command|
    $[$doc:docComment]? theorem $name :
        CAS.Numerics.RangeAll (fun j : Fin $n ↦ $t j.val = true) $start $count := $proof))

/-- The range `(start, count)` that the theorem `shard` states, a `RangeAll` with literal
bounds. -/
def shardRange (shard : Name) : MetaM (Nat × Nat) := do
  let type := (← getConstInfo shard).type
  unless type.isAppOfArity ``CAS.Numerics.RangeAll 4 do
    throwError "{shard} is not a range theorem:{indentExpr type}"
  let args := type.getAppArgs
  let some start ← (evalNat args[2]!).run
    | throwError "{shard}: the start of the range is not a numeral"
  let some count ← (evalNat args[3]!).run
    | throwError "{shard}: the length of the range is not a numeral"
  return (start, count)

/--
`cert_aggregate name : t (below := N) (shards := s, K)`

adds the theorem `name : ∀ j : Fin N, t j.val = true` from the `K` theorems `s0, …, s(K-1)`,
each a range of the family `t` as `cert_shard` states it. The ranges must be consecutive, start
at `0` and end at `N`; the command fails otherwise and names the first gap. The ranges are
joined in a balanced tree, so the proof has depth `log K`.
-/
syntax (name := certAggregate) (docComment)? "cert_aggregate " ident " : " term:max
  " (" &"below" " := " num ")" " (" &"shards" " := " ident ", " num ")" : command

elab_rules : command
  | `($[$doc:docComment]? cert_aggregate $name : $t (below := $n) (shards := $base, $k)) => do
  let shardIdent (i : Nat) : Ident := mkIdent (base.getId.appendAfter s!"{i}")
  let mut ranges : Array (Nat × Nat) := #[]
  let mut next := 0
  for i in [0:k.getNat] do
    let shard ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo (shardIdent i)
    let (start, count) ← liftTermElabM (shardRange shard)
    unless start == next do
      throwErrorAt base "{shard} starts at {start}, but the ranges before it end at {next}"
    ranges := ranges.push (start, count)
    next := start + count
  unless next == n.getNat do
    throwErrorAt k "the {k.getNat} ranges end at {next}, not at {n.getNat}"
  let proof ← if ranges.isEmpty then
      `(CAS.Numerics.rangeAll_zero)
    else joinRanges ranges (fun i ↦ pure (shardIdent i)) 0 ranges.size
  elabCommand (← `(command|
    $[$doc:docComment]? theorem $name : ∀ j : Fin $n, $t j.val = true :=
      CAS.Numerics.forall_of_rangeAll $proof))

/-! ### Data -/

/-- The balanced selection tree over `leaves[lo], …, leaves[hi - 1]`, terms of type `α`, on
the index `b`. -/
partial def selectTree (α : Expr) (leaves : Array Expr) (b : Expr) (lo hi : Nat) : Expr :=
  if hi ≤ lo + 1 then leaves[lo]!
  else
    let mid := (lo + hi) / 2
    mkApp4 (mkConst ``Bool.rec [Level.one]) (.lam `_ (mkConst ``Bool) α .default)
      (selectTree α leaves b mid hi) (selectTree α leaves b lo mid)
      (mkApp2 (mkConst ``Nat.blt) b (mkNatLit mid))

/-- The largest number of leaves of one selection tree. A lookup instantiates the whole tree of
a definition with its index, so a tree over many leaves is cut into definitions of this size. -/
def treeFan : Nat := 16

/-- The function `ℕ → α` that sends `j` to `leaves[j]`, for closed terms `leaves` of the type
`α : Type`: a selection tree for at most `treeFan` leaves, and otherwise a tree over auxiliary
definitions, each for a run of consecutive leaves, so that a lookup costs one small tree for
every level. For `j` past the end the value is one of the leaves. -/
partial def chunkedTree (α : Expr) (leaves : Array Expr) : TermElabM Expr := do
  if leaves.size ≤ treeFan then
    return .lam `j (mkConst ``Nat) (selectTree α leaves (.bvar 0) 0 leaves.size) .default
  let mut chunk := treeFan
  while chunk * treeFan < leaves.size do
    chunk := chunk * treeFan
  let natTo := mkForall `j .default (mkConst ``Nat) α
  let mut children := #[]
  for i in [0:(leaves.size + chunk - 1) / chunk] do
    let part ← chunkedTree α (leaves.extract (i * chunk) (min leaves.size ((i + 1) * chunk)))
    children := children.push
      (← mkAuxDefinitionFor (compile := true) (← mkAuxDeclName `_natTree) part)
  -- Child `j / chunk`, then leaf `j % chunk` of that child.
  let index (f : Name) : Expr := mkApp2 (mkConst f) (.bvar 0) (mkNatLit chunk)
  return .lam `j (mkConst ``Nat)
    (mkApp (selectTree natTo children (index ``Nat.div) 0 children.size) (index ``Nat.mod))
    .default

/--
`pinned_hex% w q n bytes "sha256" text`

is the function `ℕ → ℕ` from a block index to a packed natural literal, for the `n` entries of
the hexadecimal text `text`, which has one entry per line: `w / 4` digits of a `w`-bit two's
complement number, the most significant first, and a line feed. Block `b` holds the entries
`q * b` to `q * b + q - 1`, the first lowest, so entry `k < n` is read back by `blockSlot w q`,
with the bias of `signedSlot`, and `entryBall` is its ball. When `q` does not divide `n` the
last block is short; an index `k ≥ n` reads a slot of zeros, the stored form of `-2 ^ (w - 1)`,
or an entry of another block. A block of fewer than 4096 bits is an ordinary literal.

The elaborator fails unless `text` has exactly `bytes` bytes and the SHA-256 digest `sha256`
(lowercase hexadecimal, as `sha256sum` prints it), so the module names the text it was built
from, and unless the text is exactly `n` lines in the format. It reads the entries with
`hexEntry?`, the function that reads the files of a run. The literals establish nothing about
their entries.
-/
syntax (name := pinnedHex) "pinned_hex% " num num num num str term:max : term

elab_rules : term | `(pinned_hex% $w:num $q:num $n:num $bytes:num $sha:str $text) => do
  let width := w.getNat
  let perBlock := q.getNat
  unless 0 < width && width % 4 == 0 do
    throwErrorAt w "the width must be a positive multiple of 4"
  unless 0 < perBlock do
    throwErrorAt q "a block holds at least one entry"
  let data := (← evalString text).toUTF8
  unless data.size == bytes.getNat do
    throwErrorAt text "the text has {data.size} bytes, not {bytes.getNat}"
  let digest := Sha256.hex (Sha256.hash data)
  unless digest == sha.getString do
    throwErrorAt text "the SHA-256 digest of the text is {digest}, not {sha.getString}"
  unless data.size == n.getNat * (width / 4 + 1) do
    throwErrorAt text "the text has {data.size} bytes, not {n.getNat} lines of {width / 4} \
      digits and a line feed"
  let mut slots := Array.mkEmpty n.getNat
  for k in [0:n.getNat] do
    let some slot := hexEntry? width data k
      | throwErrorAt text "line {k} of the text is not {width / 4} hexadecimal digits and a \
          line feed"
    slots := slots.push slot
  let mut blocks := #[]
  for b in [0:max 1 ((n.getNat + perBlock - 1) / perBlock)] do
    let start := b * perBlock
    let packed := packSlotValues width slots start (min perBlock (n.getNat - start))
    let name ← mkAuxDeclName `_pinnedHex
    let literal ← mkCompactNatLiteral name packed
    -- The literal stays data during elaboration; kernel and compiled checks read its body.
    setReducibilityStatus name .irreducible
    blocks := blocks.push literal
  chunkedTree (mkConst ``Nat) blocks

/--
`nat_tree% [p0, p1, …]`

is the function that sends `j : ℕ` to `pj`, for terms of the type of `p0`, and every `j` past
the end to one of the terms: a tree of comparisons, cut into definitions of at most sixteen
leaves, so that selecting one of `K` terms costs about `log K` steps. The terms are natural
numbers, or functions such as the block functions of the parts of a table or the tables of a
certificate.
-/
syntax (name := natTree) "nat_tree% " "[" term,* "]" : term

elab_rules : term | `(nat_tree% [$parts,*]) => do
  if parts.getElems.isEmpty then throwError "nat_tree% needs at least one part"
  -- The type of the terms is that of the first one, which is elaborated once.
  let first ← elabTerm parts.getElems[0]! none
  synthesizeSyntheticMVarsNoPostponing
  let first ← instantiateMVars first
  let α ← instantiateMVars (← inferType first)
  let rest ← (parts.getElems.extract 1 parts.getElems.size).mapM fun part ↦ do
    let leaf ← elabTermEnsuringType part α
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars leaf
  chunkedTree α (#[first] ++ rest)

end CAS.Cert

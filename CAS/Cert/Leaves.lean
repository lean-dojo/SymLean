/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Lean.Elab.Command
public meta import Lean.Elab.Command
public meta import Lean.Meta.Basic
public meta import Lean.Structure

/-!
# The leaf conditions of a statement, listed from the environment

## Motivation

The hypothesis of a computer-assisted theorem can be one structure whose fields are again
structures, several levels deep. Which conditions does it contain in the end, how many are
there, and which of them are computations on numbers? A list made by reading can miss a field.
This module makes the list from the definitions themselves.

## The idea

Start from a proposition. A universal quantifier or an implication is entered and remembered as
a binder. A conjunction and an existential quantifier are entered. A structure of the package
under study that is a proposition is replaced by its fields. A definition of that package whose
body is again one of these forms is unfolded. Everything else is a leaf, also the structures of
other libraries (`Continuous`, `Iff`). For each leaf the command prints its path of field names,
its binders, a class and its statement.

The class is a guess from the shape of the leaf. The first rule that applies gives it:

* `INT` if an integral is reached through the definitions of the package;
* `REG` if the leaf is a regularity or measurability fact;
* `MAT` if it says that a matrix is positive or Hermitian;
* `PT` if a universally quantified variable ranges over real or complex numbers, points or
  vectors;
* `INF` if one ranges over another infinite type and no later binder puts it in a finite set.
  Natural numbers, integers and types that are parameters of the statement do not count: such
  an index is usually bounded by the next binder;
* `MAT` if a matrix occurs;
* `EQ` for an equality;
* `NUM` for an order relation or `≠`;
* `OTHER` otherwise (memberships, sorted lists, disjunctions).

## Main results

`#cert_leaves S in M` (a command, for every constant `S` whose type ends in `Prop` and every
module prefix `M`): prints the number of structures entered and of leaves, the count of each
class, and one line per leaf. It proves nothing and adds nothing to the environment.

## Relations

`cert_reduce` ([Reduce](Reduce.lean)) splits one structure and decides fields by computation.
This module only lists, through all levels. It is the general form of `#nscert_leaves` of
BlowupZoo's NSCert, which listed the 3,007 leaves of `CellLayerSystem.CellSystemCondition`;
here the package is a parameter with a default, and conditions declared in the current module
are entered too. [Structure](../Examples/Cert/Structure.lean) runs it on a structure with
fields of five classes.

## Scope

The classes are a reading aid and not a proof of anything: a leaf marked `NUM` can still hide a
function behind a name, and a leaf marked `INF` can be bounded in a way that the guess does not
see. A definition that is not unfolded can hide further conditions; the report counts the
definitions that were unfolded. The names of the integral, regularity and matrix notions are
compared as names, so this module imports none of their theories and does not check that they
exist.
-/

public meta section

namespace CAS.Cert

open Lean Meta Elab Command

/-- One leaf condition. -/
structure Leaf where
  /-- field names from the root, separated by dots -/
  path : String
  /-- the binders above the leaf, outermost first -/
  binders : Array String
  /-- the number of existential quantifiers above the leaf -/
  witnesses : Nat
  /-- the guessed class -/
  cls : String
  /-- the head symbol of the statement -/
  head : String
  /-- the statement on one line -/
  stmt : String

/-- The state of a walk. -/
structure LeafState where
  /-- the leaves found so far, in the order of the walk -/
  leaves : Array Leaf := #[]
  /-- structures that were replaced by their fields -/
  structs : NameSet := {}
  /-- the fields of these structures that are propositions, as `structure.field` -/
  fields : NameSet := {}
  /-- definitions that were unfolded -/
  unfolded : NameSet := {}
  /-- cache: does a constant reach an integral through definitions of the package? -/
  integral : Std.HashMap Name Bool := {}

/-- The monad of a walk. -/
abbrev LeafM := StateRefT LeafState MetaM

/-- Is the constant declared in a module whose name starts with `pre`, or in the module that is
being elaborated? -/
def inPackage (pre : Name) (c : Name) : CoreM Bool := do
  let env ← getEnv
  match env.getModuleIdxFor? c with
  | some i => return pre.isPrefixOf env.header.moduleNames[i.toNat]!
  | none => return env.contains c

/-- The constants that mark an integral. -/
def integralMarks : List Name :=
  [`MeasureTheory.lintegral, `MeasureTheory.integral, `intervalIntegral]

/-- Does `c` reach an integral through the bodies of definitions of the package `pre`? -/
partial def reachesIntegral (pre : Name) (c : Name) : LeafM Bool := do
  if integralMarks.contains c then return true
  if let some b := (← get).integral[c]? then return b
  modify fun s ↦ { s with integral := s.integral.insert c false }
  let mut ans := false
  if ← inPackage pre c then
    if let some (.defnInfo d) := (← getEnv).find? c then
      for u in d.value.getUsedConstants do
        if ← reachesIntegral pre u then
          ans := true
          break
  modify fun s ↦ { s with integral := s.integral.insert c ans }
  return ans

/-- Heads of regularity and measurability facts. -/
def regularityHeads : List Name :=
  [`Continuous, `ContinuousOn, `ContDiff, `ContDiffOn, `Differentiable, `DifferentiableOn,
    `Measurable, `MeasureTheory.StronglyMeasurable, `MeasureTheory.AEStronglyMeasurable,
    `AEMeasurable, `LipschitzWith, `LipschitzOnWith, `MeasureTheory.Integrable,
    `MeasureTheory.MemLp, `Function.Periodic, `MeasurableSet]

/-- Heads of facts about matrices. -/
def matrixHeads : List Name :=
  [`Matrix.PosDef, `Matrix.PosSemidef, `Matrix.IsHermitian, `Matrix.IsSymm]

/-- The kind of a universally quantified variable of type `t`: `0` if it is harmless (a
proposition, a type with a `Fintype` instance, `ℕ`, `ℤ`, or a type that is a parameter of the
statement: such an index is usually bounded by the next binder or meant to be finite), `2` if the
type mentions the real or the complex numbers, `1` otherwise. -/
def binderKind (t : Expr) : MetaM Nat := do
  if ← isProp t then return 0
  let t' ← whnfR t
  if t'.isFVar || t'.isConstOf ``Nat || t'.isConstOf ``Int then return 0
  let cs := t.getUsedConstants ++ t'.getUsedConstants
  if cs.contains `Real || cs.contains `Complex then return 2
  let u ← getLevel t
  let inst ← try synthInstance? (mkApp (mkConst `Fintype [u.dec.getD Level.zero]) t)
    catch _ => pure none
  return if inst.isSome then 0 else 1

/-- Does the proposition `h` put the variable `x` in a finite set or a list? -/
def boundsVar (x : Expr) (h : Expr) : Bool :=
  match_expr h with
  | Membership.mem _ γ _ _ elem => elem == x && (γ.isAppOf `Finset || γ.isAppOf ``List)
  | _ => false

/-- The guessed class of the leaf `e` under the binders `xs` (variables of universal and
existential quantifiers and hypotheses, outermost first; `univ` says which are universal). -/
def classify (pre : Name) (xs : Array Expr) (univ : Array Bool) (e : Expr) : LeafM String := do
  let types ← xs.mapM (inferType ·)
  let mut consts := e.getUsedConstants
  for t in types do
    consts := consts ++ t.getUsedConstants
  for c in consts do
    if ← reachesIntegral pre c then return "INT"
  let head := e.getAppFn.constName?.getD .anonymous
  if regularityHeads.contains head then return "REG"
  if matrixHeads.contains head then return "MAT"
  let mut unbounded := false
  for i in [0:xs.size] do
    if univ[i]! then
      let kind ← binderKind types[i]!
      if kind == 2 then return "PT"
      if kind == 1 && !(types.extract (i + 1) types.size).any (boundsVar xs[i]!) then
        unbounded := true
  if unbounded then return "INF"
  if consts.contains `Matrix || matrixHeads.contains head then return "MAT"
  if head == ``Eq then return "EQ"
  if [``LE.le, ``LT.lt, ``GE.ge, ``GT.gt, ``Ne].contains head then return "NUM"
  return "OTHER"

/-- Replaces every run of white space by one space and drops it at the start. -/
def squeeze (s : String) : String :=
  (s.foldl (fun (acc : String × Bool) c =>
    if c.isWhitespace then (if acc.2 then acc else (acc.1.push ' ', true))
    else (acc.1.push c, false)) ("", true)).1

/-- The first `n` characters of a string, with a mark if something was cut. -/
def cut (s : String) (n : Nat) : String :=
  if s.length ≤ n then s
  else (s.foldl (fun (acc : String × Nat) c =>
    if acc.2 < n then (acc.1.push c, acc.2 + 1) else acc) ("", 0)).1 ++ " ..."

/-- A statement or a type on one line, cut at `n` characters. -/
def oneLine (e : Expr) (n : Nat := 240) : MetaM String := do
  return cut (squeeze ((← ppExpr e).pretty 100000)) n

/-- Is `e` of a form that the walk enters: a binder, a conjunction, an existential quantifier or
a structure of the package that is a proposition? -/
def isEntered (pre : Name) (e : Expr) : MetaM Bool := do
  let e := e.consumeMData
  if e.isForall then return true
  if e.isAppOf ``And || e.isAppOf ``Exists then return true
  match e.getAppFn.constName? with
  | some c => return isStructure (← getEnv) c && (← isProp e) && (← inPackage pre c)
  | none => return false

/-- The walk: collects the leaves of the proposition `e`. `xs` are the binders above `e`
(variables and hypotheses), `univ` says which of them come from a universal quantifier or an
implication, and `bs` are their printed forms. -/
partial def walk (pre : Name) (e : Expr) (path : String) (xs : Array Expr) (univ : Array Bool)
    (bs : Array String) : LeafM Unit := do
  let e := (← instantiateMVars e).consumeMData
  if e.isForall then
    forallBoundedTelescope e (some 1) fun ys body ↦ do
      let t ← inferType ys[0]!
      let name := (← ys[0]!.fvarId!.getUserName).eraseMacroScopes
      let shown ← if ← isProp t then oneLine t 120 else pure s!"∀ {name} : {← oneLine t 120}"
      walk pre body path (xs.push ys[0]!) (univ.push true) (bs.push shown)
    return
  match_expr e with
  | And a b =>
    walk pre a (path ++ "/1") xs univ bs
    walk pre b (path ++ "/2") xs univ bs
    return
  | Exists α p =>
    let p' := if p.isLambda then p
      else mkLambda `x .default α (mkApp (p.liftLooseBVars 0 1) (.bvar 0))
    lambdaBoundedTelescope p' 1 fun ys body ↦ do
      let name := (← ys[0]!.fvarId!.getUserName).eraseMacroScopes
      walk pre body path (xs.push ys[0]!) (univ.push false)
        (bs.push s!"∃ {name} : {← oneLine α 120}")
    return
  | _ => pure ()
  let env ← getEnv
  if let some c := e.getAppFn.constName? then
    if isStructure env c && (← isProp e) && (← inPackage pre c) then
      modify fun s ↦ { s with structs := s.structs.insert c }
      let ctor := getStructureCtor env c
      let ctorType := ctor.type.instantiateLevelParams ctor.levelParams e.getAppFn.constLevels!
      let fieldsType ← instantiateForall ctorType (e.getAppArgs.extract 0 ctor.numParams)
      forallTelescope fieldsType fun fs _ ↦ do
        for f in fs do
          let t ← inferType f
          if ← isProp t then
            let name := (← f.fvarId!.getUserName).eraseMacroScopes
            modify fun s ↦ { s with fields := s.fields.insert (c ++ name) }
            walk pre t (if path.isEmpty then toString name else path ++ "." ++ toString name)
              xs univ bs
      return
    if ← inPackage pre c then
      if let some e' ← unfoldDefinition? e then
        let e' := e'.headBeta
        if ← isEntered pre e' then
          modify fun s ↦ { s with unfolded := s.unfolded.insert c }
          walk pre e' path xs univ bs
          return
  let cls ← classify pre xs univ e
  let witnesses := (univ.filter (!·)).size
  let head := match e.getAppFn.constName? with
    | some c => toString c
    | none => "-"
  let leaf : Leaf := { path, binders := bs, witnesses, cls, head, stmt := ← oneLine e }
  modify fun s ↦ { s with leaves := s.leaves.push leaf }

/--
`#cert_leaves S in M`

lists the leaf conditions of `S`, a constant whose type ends in `Prop` (a structure of
conditions or a definition): its parameters become variables, and the walk enters binders,
conjunctions, existential quantifiers and structures that are propositions, and unfolds the
definitions of the modules whose name starts with `M` and of the current module. Without
`in M`, `M` is the first component of the name of the module that declares `S`. It prints the
counts and then one line per leaf, with tabs between the word `LEAF`, the index, the class, the
number of existential quantifiers above the leaf, the path, the head symbol, the binders and
the statement. It proves nothing and adds nothing to the environment.
-/
syntax (name := certLeaves) "#cert_leaves " ident (" in " ident)? : command

elab_rules : command | `(command| #cert_leaves $s $[in $m]?) => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo s
  let env ← getEnv
  let pre : Name := match m with
    | some m => m.getId
    | none => match env.getModuleIdxFor? c with
      | some i => env.header.moduleNames[i.toNat]!.getRoot
      | none => env.mainModule.getRoot
  let st ← liftTermElabM do
    let info ← getConstInfo c
    forallTelescope info.type fun xs body ↦ do
      unless body.isProp do
        throwError "#cert_leaves: `{c}` is not a family of propositions"
      let e := mkAppN (mkConst c (info.levelParams.map mkLevelParam)) xs
      let ((), st) ← (walk pre e "" #[] #[] #[]).run {}
      return st
  let classes := ["NUM", "EQ", "MAT", "INF", "PT", "INT", "REG", "OTHER"]
  let counts := classes.map fun k ↦ s!"{k} {(st.leaves.filter (·.cls == k)).size}"
  let mut out := s!"leaves of {c}\n\
    structures entered: {st.structs.size}, their fields: {st.fields.size}, \
    definitions unfolded: {st.unfolded.size}, leaves: {st.leaves.size}, \
    leaves under an existential quantifier: {(st.leaves.filter (·.witnesses > 0)).size}\n\
    classes: {", ".intercalate counts}\n"
  let mut i := 0
  for l in st.leaves do
    i := i + 1
    out := out ++ s!"LEAF\t{i}\t{l.cls}\t{l.witnesses}\t{l.path}\t{l.head}\t\
      {" ; ".intercalate l.binders.toList}\t{l.stmt}\n"
  logInfo out

end CAS.Cert

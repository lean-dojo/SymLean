/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
/-!
The duplicate gate of `scripts/dups.sh`, which runs this file after an `import` of every module
under `CAS/`. It prints six counts and their lists, one item per line:

* `DUPDEF`: groups of library definitions of functions with the same type and value (a value of
  a type that is not a function type, such as a numeric limit, is not counted);
* `DUPTHM`: groups of library theorems with the same statement;
* `RESTATE`: library theorems whose statement is that of a theorem outside SymLean;
* `UNUSED`: library declarations that no declaration of SymLean uses (examples included) and that
  nothing else is known to use: not an instance, a `simp` or `csimp` lemma; not registered in a
  table that Lean or SymLean reads (an elaborator, a macro, an unexpander, the target of
  `implemented_by`, a route or a goal predicate of `@[cas_route]`); not a declaration that
  `scripts/dups.targets` lists by name with its reason; not a declaration that a downstream
  project references or cites (`scripts/downstream.names`); and, by `scripts/dups_check.py`, not
  named in a source file of SymLean outside its own declaration;
* `EQUIV`: library theorems `∀ xs, c₁ xs = c₂ xs` or `↔` between two definitions, at least one of
  them in the library, applied to exactly the bound variables;
* `MISSING`: names of `scripts/downstream.names` that are no longer constants: a deletion or a
  rename that a downstream project would meet.

The library is `CAS` without `CAS.Examples`. Statements and values are compared as terms, up to
the names of bound variables and of universe parameters; a name quoted in meta code (``n``) is
a use of `n`. Proofs count: theorem bodies are read with `allowOpaque`. Generated declarations
(`_proof_n`, matchers, `eq_n`, `eq_def`, the equation `T.brecOn.eq` of an auxiliary recursor, the
constructor index `T.ctorIdx` that Lean generates for every inductive type `T`, reserved names
such as `f.congr_simp`, the `T.ext_iff` of a lemma `T.ext` that is registered with `@[ext]`, the
`quot`, `parenthesizer` and `formatter` declarations of a syntax category or parser, recognized
by their types, and the like) are not counted. The candidates of every list are the public
definitions and theorems of the library: a private declaration is skipped, and so is a constant
that is neither (a type, a structure, the opaque constant of a `partial def`). The two lists
are required: the run fails when `scripts/dups.targets` or `scripts/downstream.names` cannot be
read or the second is empty.
-/

open Lean Meta Compiler

/-- The name that `Name.mkStr p s`, `Name.str p s`, `Name.mkStr1 s₁` … `Name.mkStr8 s₁ … s₈` or
`Name.anonymous` builds from string literals, as quoted names elaborate. -/
partial def nameLiteral? (e : Expr) : Option Name :=
  if e.isConstOf ``Name.anonymous then some .anonymous else
  match e.getAppFn with
  | .const c _ =>
    let args := e.getAppArgs
    let strings := args.filterMap fun
      | .lit (.strVal s) => some s
      | _ => none
    if (c == ``Name.mkStr || c == ``Name.str) && args.size == 2 then
      match nameLiteral? args[0]!, args[1]! with
      | some p, .lit (.strVal s) => some (p.str s)
      | _, _ => none
    else if [``Name.mkStr1, ``Name.mkStr2, ``Name.mkStr3, ``Name.mkStr4, ``Name.mkStr5,
        ``Name.mkStr6, ``Name.mkStr7, ``Name.mkStr8].contains c && 0 < args.size &&
        strings.size == args.size then
      some (strings.foldl Name.str .anonymous)
    else none
  | _ => none

/-- Whether `c` is a constant applied to exactly the bound variables `#(n - 1) … #0`. -/
def appliedToBVars (n : Nat) (e : Expr) : Option Name :=
  match e.getAppFn with
  | .const c _ =>
    let args := e.getAppArgs
    if args.size == n && (List.range n).all fun k ↦ args[k]! == .bvar (n - 1 - k) then some c
    else none
  | _ => none

/-- The groups of more than one name in `m`, each as one sorted, comma-separated line. -/
def groupsOf {α : Type} [BEq α] [Hashable α] (m : Std.HashMap α (Array Name)) : Array String :=
  m.fold (init := #[]) fun acc _ names ↦
    if names.size > 1 then
      acc.push (", ".intercalate ((names.qsort (·.toString < ·.toString)).toList.map toString))
    else acc

/-- The body of `∀ x₁ … xₙ, b` and `n`. -/
def stripForall : Expr → Nat → Expr × Nat
  | .forallE _ _ b _, n => stripForall b (n + 1)
  | e, n => (e, n)

#eval show MetaM Unit from do
  let env ← getEnv
  let modOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).map fun i ↦ env.header.moduleNames[i.toNat]!
  let ours (n : Name) := (modOf n).any (·.getRoot == `CAS)
  let lib (n : Name) := (modOf n).any fun m ↦ m.getRoot == `CAS && !(`CAS.Examples).isPrefixOf m
  -- The extensionality lemmas registered with `@[ext]`; each generates its `ext_iff`.
  let extLemmas : NameSet :=
    (Lean.Meta.Ext.extExtension.getState env).tree.values.foldl (·.insert ·.declName) {}
  let skip (n : Name) (c : ConstantInfo) := n.isInternalDetail || isAuxRecursor env n ||
    isNoConfusion env n ||
    (env.isProjectionFn n) || isMatcherCore env n || (isCtorIdxCore? env n).isSome ||
    isReservedName env n || (`Lean.Parser.Category).isPrefixOf n ||
    (match n with
      | .str p s => s == "eq_def" || s == "eq_unfold" || s == "induct" || s == "fun_cases" ||
          (s == "eq" && isAuxRecursor env p) ||
          -- What `declare_syntax_cat` and `syntax` generate next to a parser, by their types.
          (s == "quot" && c.type.isConstOf ``Lean.ParserDescr) ||
          (s == "parenthesizer" && c.type.isConstOf ``Lean.PrettyPrinter.Parenthesizer) ||
          (s == "formatter" && c.type.isConstOf ``Lean.PrettyPrinter.Formatter) ||
          -- The equivalence that `@[ext]` generates next to a registered lemma `T.ext`.
          (s == "ext_iff" && extLemmas.contains (p.str "ext"))
      | _ => false)
  let canon (c : ConstantInfo) (e : Expr) : Expr :=
    e.instantiateLevelParams c.levelParams
      (c.levelParams.mapIdx fun i _ ↦ .param (.mkSimple s!"u{i}"))
  -- The declarations that count as used although nothing here uses them, each listed by name
  -- with its reason.
  let targets : NameSet := (← IO.FS.readFile "scripts/dups.targets").splitOn "\n" |>.foldl
    (init := {}) fun s line ↦
      let line := String.ofList ((line.splitOn "#").head!.toList.filter fun ch ↦ !ch.isWhitespace)
      if line.isEmpty then s else s.insert line.toName
  -- The declarations that the built downstream projects reference: the first word of each line.
  let downstream : Array Name :=
    ((← IO.FS.readFile "scripts/downstream.names").splitOn "\n").toArray.filterMap fun line ↦
      match ((line.splitOn "#").head!.splitOn " ").head! with
      | "" => none
      | word => some word.toName
  if downstream.isEmpty then throwError "scripts/downstream.names lists no declaration"
  let missing := (downstream.filter fun n ↦ !env.contains n).map toString |>.qsort (· < ·)
  -- The declarations that a table names: Lean's elaborators, macros and unexpanders, and the
  -- routes and goal predicates of `@[cas_route]`.
  let mut registered : NameSet := downstream.foldl (·.insert ·) {}
  for names in [(Elab.Term.termElabAttribute.ext.getState env).declNames,
      (Elab.Command.commandElabAttribute.ext.getState env).declNames,
      (Elab.Tactic.tacticElabAttribute.ext.getState env).declNames,
      (Elab.macroAttribute.ext.getState env).declNames,
      (PrettyPrinter.Delaborator.delabAttribute.ext.getState env).declNames,
      (PrettyPrinter.Delaborator.appUnexpanderAttribute.ext.getState env).declNames] do
    registered := names.fold (·.insert ·) registered
  for registration in CAS.Tactic.RouteRegistry.registrations env do
    registered := registered.insert registration.declaration
    if let some goal := registration.goal? then registered := registered.insert goal
  let simpLemmas := (simpExtension.getState env).lemmaNames
  let mut defs : Std.HashMap (Expr × Expr) (Array Name) := {}
  let mut thms : Std.HashMap Expr (Array Name) := {}
  let mut external : Std.HashMap Expr Name := {}
  let mut used : NameSet := {}
  let mut candidates : Array Name := #[]
  let mut equivs : Array String := #[]
  for (n, c) in env.constants.map₁.toList do
    let isOurs := ours n
    if isOurs then
      -- The compiled implementation of `n` is used by `n`.
      if let some impl := getImplementedBy? env n then used := used.insert impl
      let value? := c.value? (allowOpaque := true)
      for m in c.type.getUsedConstants ++ (value?.map (·.getUsedConstants)).getD #[] do
        if m != n then used := used.insert m
      if let some value := value? then
        let found ← IO.mkRef ({} : NameSet)
        value.forEachWhere (fun e ↦ e.isApp && (e.getAppFn.isConst))
          (fun e ↦ do if let some m := nameLiteral? e then found.modify (·.insert m))
          (stopWhenVisited := false)
        for m in (← found.get).toList do used := used.insert m
    if skip n c then continue
    match c with
    | .defnInfo d =>
        if lib n then
          candidates := candidates.push n
          if d.type.isForall then
            let key := (canon c d.type, canon c d.value)
            defs := defs.insert key ((defs.getD key #[]).push n)
    | .thmInfo t =>
        let type := canon c t.type
        if lib n then
          thms := thms.insert type ((thms.getD type #[]).push n)
          candidates := candidates.push n
          let (body, k) := stripForall t.type 0
          let sides? : Option (Expr × Expr) :=
            if body.isAppOfArity ``Eq 3 then some (body.appFn!.appArg!, body.appArg!)
            else if body.isAppOfArity ``Iff 2 then some (body.appFn!.appArg!, body.appArg!)
            else none
          if let some (lhs, rhs) := sides? then
            if let (some c₁, some c₂) := (appliedToBVars k lhs, appliedToBVars k rhs) then
              let isDef (c : Name) := (env.find? c).any (·.isDefinition)
              if c₁ != c₂ && isDef c₁ && isDef c₂ && (lib c₁ || lib c₂) then
                equivs := equivs.push s!"{n}: {c₁} ~ {c₂}"
        else if !isOurs then
          external := external.insert type n
    | _ => pure ()
  let dupDefs := (groupsOf defs).qsort (· < ·)
  let dupThms := (groupsOf thms).qsort (· < ·)
  let restated := (thms.fold (init := #[]) fun acc type names ↦
      match external[type]? with
      | some e => names.foldl (fun acc n ↦ acc.push s!"{n} = {e}") acc
      | none => acc).qsort (· < ·)
  let unused := (candidates.filter fun n ↦
      !used.contains n && !isInstanceCore env n && !hasCSimpAttribute env n &&
      !simpLemmas.contains (.decl n) && !targets.contains n &&
      !registered.contains n).map toString |>.qsort (· < ·)
  let equivLines := equivs.qsort (· < ·)
  IO.println s!"DUPDEF {dupDefs.size}"
  IO.println s!"DUPTHM {dupThms.size}"
  IO.println s!"RESTATE {restated.size}"
  IO.println s!"UNUSED {unused.size}"
  IO.println s!"EQUIV {equivLines.size}"
  IO.println s!"MISSING {missing.size}"
  for (tag, list) in [("DUPDEF", dupDefs), ("DUPTHM", dupThms), ("RESTATE", restated),
      ("UNUSED", unused), ("EQUIV", equivLines), ("MISSING", missing)] do
    for line in list do IO.println s!"{tag}: {line}"

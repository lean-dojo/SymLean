/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
public import FloatLib.Floats.Formats.BinaryInterchange.Format.Properties
public import CAS.Command.Syntax
public import CAS.Tactic.KernelReadBack
import FloatLib.Numerics.Enclosure.Expression.Basic

/-!
# The arithmetic of a CEGA call

## Motivation

How does a user say that `cega` should compute its enclosures with IEEE floats of a chosen
format instead of exact rationals, for one call or for a whole section, and how does that
choice reach the place where the query is built?

## The idea

The arithmetic of a call is either exact, the default, or an IEEE binary format of FloatLib.
Every IEEE binary format is fixed by two numbers, the bits of its exponent and of its fraction,
so a float arithmetic is carried as those two numbers and the name the user wrote. A call gives
its arithmetic by the flag `use_floats` and by the item `(arith := F)`, and the option
`cega.arithmetic` gives the default of a section, or of a whole build when a lakefile passes it
to every module; the item wins over the flag, and the flag over the option. `F` is any term of
type `FloatFormat`, elaborated with FloatLib's format names in scope, or a string with the text
that the option takes: `exact`, the text of such a term, or `binary(p := N, emax := M)`, the
name of a format by its precision and largest exponent as in IEEE 754. The kernel evaluates the
two widths of the term and whether it is an IEEE format, and a format that is not is refused.
`cega` sets the arithmetic that it resolved around its routes, in an internal option, and the box
queries of `CAS.CEGA.Elaboration` read it where they build their term. The `#cas` commands and
`cas` never set it, so they compute with exact rationals.

## Main definitions

* `Arithmetic`: exact, or the IEEE binary format with given exponent and fraction widths.
* `cega.arithmetic`: the option that sets the arithmetic of the `cega` calls of a section.
* `ArithmeticRequest`, `ArithmeticRequest.resolve`: what one call says, and the arithmetic that
  follows from it and from the option.
* `parseArithmeticText`, `parseArithmeticItem`: a format read from a string and from the value
  of `(arith := F)`.
* `widthsOfPrecision?`: the exponent and fraction widths of the IEEE format with precision `p`
  and largest exponent `emax`.
* `activeArithmetic`, `withArithmetic`: the arithmetic of the running `cega` call.
* `formatTerms`: the closed terms `FloatFormat.ieee e f` and its proof of `isIEEE`.
* `splitArithmeticItem`: a configuration group without its item `(arith := F)`.
* `exactByOption`, `exactItemText`: whether the option of the section asks for exact
  arithmetic, and the item that a printed call of an exact route needs when it does not.
* `FloatFailure`: why a float query has no result, as FloatLib's diagnosis of its evaluation
  reports it.
* `floatFailure`, `Arithmetic.remedy`, `arithmeticNote`: the words for a float query without a
  result, and the calls to try next.
* `Arithmetic.suffix`: the words that name a float format in the `trace.cega.stated` output.

## Relations

`formatTerms` builds the format and the proof that `CAS.CEGA.encloseBoxFloat?` takes, so a float
query is in reach of `boundOn_of_check` and the other check theorems of `CAS.CEGA.Query`.
`CAS.CEGA` resolves the arithmetic of each call (`resolveArithmetic`, `bareConfig`) and sets it
with `withArithmetic`; `CAS.CEGA.Elaboration` reads it where it builds the query
(`boxQueryTerm`), where it adds a theorem and where it reports a failure
(`queryFailureMessage`, which reads a `FloatFailure` back from the kernel);
`CAS.Tactic.BoxInequality` writes it into replays and advice; and `CAS.Reporting` prints it under
a `cega?` suggestion. `CAS.Examples.CEGA.Floats` has a call of every form, and `tests/floats` a
build of each kind.

## Implementation notes

This module imports FloatLib's formats, and the operations of FloatLib's expressions for the
names that a `FloatFailure` carries, and nothing of FloatLib's float arithmetic. The float query
and its diagnosis are in `CAS.CEGA.FloatQuery`, which `CAS.CEGA` imports, and
`CAS.CEGA.Elaboration` names them without importing them (`floatQueryName`,
`floatDiagnosisName`), so that the modules that use only the kernel checks of the elaboration
layer, such as the certificate framework `CAS.Cert`, do not load FloatLib's float arithmetic.

The resolved arithmetic travels in the option `cega.activeArithmetic`, as `cega.nativePolynomial`
does for native `cega [fast]`: options are scoped to the running tactic and to its thread, which
a global reference is not. A float query is built with `FloatFormat.ieee e f` whatever name the
user wrote, so its proof of `isIEEE` is FloatLib's `FloatFormat.isIEEE_ieee` and needs no
evaluation; the name is kept for messages and for the calls that `cega?` suggests.

## Scope

Only IEEE formats are accepted, and the float query takes a proof that its format is one. Its
enclosures do not need that proof: FloatLib's outward rounding `ExecFloat.Binary.intervalRounding`,
on which the query computes, checks each end it returns with exact rationals, in every binary
format. So the formats without infinities or with one NaN (`FloatFormat.finite`, `finiteMaxNaN`,
`finiteUnsignedZero`) could be accepted as well.
-/

public meta section

namespace CAS.CEGA.Elaboration

open Lean Elab Term Meta
open FloatLib.Floats.Formats.BinaryInterchange

/-- The arithmetic in which a CEGA box query computes its enclosure. -/
inductive Arithmetic where
  /-- Exact integers and rationals: the planner of `CAS.CEGA.Query`. The default. -/
  | exact
  /-- Intervals whose ends are numbers of the IEEE binary format with `expWidth` exponent bits
  and `fracWidth` fraction bits, `FloatFormat.ieee expWidth fracWidth`. `name` is the format as
  the user wrote it, for messages and for the calls that `cega?` suggests. -/
  | float (name : String) (expWidth fracWidth : Nat)
deriving Repr, BEq, Inhabited

namespace Arithmetic

/-- Whether the arithmetic is a float format. -/
def isFloat : Arithmetic → Bool
  | .exact => false
  | .float .. => true

/-- The arithmetic in words, as the report of `cega?` prints it. -/
def describe : Arithmetic → String
  | .exact => "exact rationals"
  | .float name .. => s!"{name} floating point"

/-- The words that name a float arithmetic after the kind of a query in the `trace.cega.stated`
output, as ` in binary64` in `bound query in binary64`; nothing for exact arithmetic, whose
traces are the ones that it has without this option. -/
def suffix : Arithmetic → String
  | .exact => ""
  | .float name .. => s!" in {name}"

/-- The arithmetic as the value of the internal option `cega.activeArithmetic`: the empty
string for exact arithmetic, and `e:f:name` for a float format. -/
def encode : Arithmetic → String
  | .exact => ""
  | .float name expWidth fracWidth => s!"{expWidth}:{fracWidth}:{name}"

/-- The arithmetic that `encode` wrote; any other text, and widths that no format has, are exact
arithmetic. -/
def decode (text : String) : Arithmetic :=
  match text.splitOn ":" with
  | expWidth :: fracWidth :: name =>
      match expWidth.toNat?, fracWidth.toNat? with
      | some e, some f => if 2 ≤ e ∧ 1 ≤ f then .float (":".intercalate name) e f else .exact
      | _, _ => .exact
  | _ => .exact

end Arithmetic

/-- The arithmetic of the enclosures that `cega` and `cega?` compute in a section: `"exact"`,
the default, for integers and rationals, or an IEEE binary format of FloatLib, such as
`"binary64"`, `"binary128"`, `"FloatFormat.ieee 15 112"` or
`"binary(p := 113, emax := 16383)"`, for intervals whose ends are floats of that format, rounded
outward and checked in the kernel. A call overrides it with the flag `[use_floats := false]` or
`[use_floats := true]` and with the item `(arith := F)`. A project sets it for every module of a
build with `weak.cega.arithmetic` in the Lean options of its lakefile, as in
``leanOptions := #[⟨`weak.cega.arithmetic, "binary64"⟩]``. The `#cas` commands and `cas` compute
with exact rationals whatever its value. -/
register_option cega.arithmetic : String := {
  defValue := "exact"
  descr := "the arithmetic of `cega` enclosures: \"exact\" (integers and rationals) or a \
    FloatLib IEEE binary format such as \"binary64\""
}

/-- Set by `cega` around its routes to the arithmetic that it resolved from the call and from
`cega.arithmetic` (`Arithmetic.encode`); the box queries read it where they build their term. It
is internal: the user setting is `cega.arithmetic`. -/
register_option cega.activeArithmetic : String := {
  defValue := ""
  descr := "internal: the arithmetic that the running `cega` call resolved; not a user setting"
}

/-- The arithmetic of the running `cega` call; exact outside one. -/
def activeArithmetic {m : Type → Type} [Monad m] [MonadOptions m] : m Arithmetic :=
  return .decode (cega.activeArithmetic.get (← getOptions))

/-- Run `action` with `arithmetic` as the arithmetic of its box queries. -/
def withArithmetic {m : Type → Type} {α : Type} [MonadWithOptions m] (arithmetic : Arithmetic)
    (action : m α) : m α :=
  withOptions (fun options ↦ cega.activeArithmetic.set options arithmetic.encode) action

/-- The closed terms `FloatFormat.ieee e f` and the proof that it is an IEEE format, for
`2 ≤ e` and `1 ≤ f`: the format and the hypothesis that `CAS.CEGA.encloseBoxFloat?` takes. -/
def formatTerms (expWidth fracWidth : Nat) : MetaM (Expr × Expr) := do
  let e := mkNatLit expWidth
  let f := mkNatLit fracWidth
  let he ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit 2, e])
  let hf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, f])
  return (mkApp4 (mkConst ``FloatFormat.ieee) e f he hf,
    mkApp4 (mkConst ``FloatFormat.isIEEE_ieee) e f he hf)

/-! ## Reading a format -/

/-- The exponent and fraction widths of the IEEE binary format with precision `p`, the bits of
a significand with its leading bit, and largest exponent `emax`, the two parameters by which
IEEE 754 names a binary format: `p - 1` fraction bits and `log₂ (emax + 1) + 1` exponent bits.
`none` unless `p ≥ 2` and `emax + 1` is a power of two that is at least two. -/
def widthsOfPrecision? (p emax : Nat) : Option (Nat × Nat) :=
  let expWidth := Nat.log2 (emax + 1) + 1
  if 2 ≤ p ∧ 1 ≤ emax ∧ emax + 1 = 2 ^ (expWidth - 1) then some (expWidth, p - 1) else none

/-- `text` without the white space at its two ends. -/
private def trimmed (text : String) : String :=
  String.ofList
    ((text.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

/-- The numbers `p` and `emax` of a text `binary(p := p, emax := emax)`, with any spacing. -/
def precisionForm? (text : String) : Option (Nat × Nat) := do
  let compact := String.ofList (text.toList.filter (!·.isWhitespace))
  let head := "binary(p:="
  unless compact.startsWith head && compact.endsWith ")" do none
  let body := String.ofList (compact.toList.drop head.length).dropLast
  match body.splitOn ",emax:=" with
  | [p, emax] => pure (← p.toNat?, ← emax.toNat?)
  | _ => none

/-- The formats that a refusal lists as examples. -/
private def formatExamples : String :=
  "`binary16`, `binary32`, `binary64`, `binary128`, `FloatFormat.ieee e f` for `e` exponent \
   bits and `f` fraction bits, or `\"binary(p := 113, emax := 16383)\"` for a precision and a \
   largest exponent"

/-- FloatLib's namespace of binary formats, where `FloatFormat` and its catalog live. -/
private def formatScope : Name := `FloatLib.Floats.Formats.BinaryInterchange

/-- The format of FloatLib's catalog that the identifier `stx` names: the constant
`FloatFormat.n`, or `n`, of FloatLib's namespace of binary formats, when it has the type
`FloatFormat`. These names are read before any other, so that `binary64` is FloatLib's binary64
wherever `cega` runs: inside a theorem `bound.binary64`, where Lean reads `binary64` as that
theorem, and next to a local variable or a declaration of the same name. -/
private def catalogFormat? (stx : Syntax) : CoreM (Option Expr) := do
  unless stx.isIdent do
    return none
  let name := stx.getId.eraseMacroScopes
  for candidate in [formatScope ++ `FloatFormat ++ name, formatScope ++ name] do
    if let some info := (← getEnv).find? candidate then
      if info.type.isConstOf ``FloatFormat ∧ info.levelParams.isEmpty then
        return some (Lean.mkConst candidate)
  return none

/-- The float arithmetic of the format `stx`: a name of FloatLib's catalog (`catalogFormat?`),
or else a term of type `FloatFormat` elaborated with the names of FloatLib's formats in scope,
so that `binary64` and `ieee 15 112` are read as `FloatFormat.binary64` and
`FloatFormat.ieee 15 112`. The term is elaborated without the local context, since a format is a
closed term, so no hypothesis or variable of the goal can take its names. The kernel evaluates
its exponent width, its fraction width and whether it is an IEEE format; a format that is not
IEEE is refused. `name` is the format as the user wrote it. -/
def elabFormat (stx : Syntax) (name : String) : TermElabM Arithmetic := do
  let opened : List OpenDecl :=
    [.simple formatScope [], .simple (formatScope ++ `FloatFormat) []]
  let format ← match ← catalogFormat? stx with
    | some format => pure format
    | none =>
        withLCtx {} {} <| withTheReader Core.Context
            (fun context ↦ { context with openDecls := opened ++ context.openDecls }) do
          try
            -- An elaboration error is the refusal: no placeholder term stands in for the format.
            Term.withoutErrToSorry do
              let format ← Term.elabTermEnsuringType stx (Lean.mkConst ``FloatFormat)
              Term.synthesizeSyntheticMVarsNoPostponing
              instantiateMVars format
          catch error =>
            throwErrorAt stx "`{name}` is not a FloatLib binary format; the arithmetic of \
              `cega` is `\"exact\"` or a format such as {formatExamples}. A format is a closed \
              term: the variables and hypotheses of the goal are not in its scope.\
              {indentD error.toMessageData}"
  if format.hasFVar ∨ format.hasMVar ∨ format.hasSorry then
    throwErrorAt stx "the format `{name}` of the arithmetic is not a closed term of type \
      `FloatFormat`"
  let natural (field : Name) : MetaM Nat := do
    let reduced ← Tactic.KernelReadBack.kernelWhnf (mkApp (Lean.mkConst field) format)
      "the format of the arithmetic"
    let some value := reduced.rawNatLit? <|> reduced.nat?
      | throwErrorAt stx "the widths of the format `{name}` did not reduce to numerals"
    return value
  let expWidth ← natural ``FloatFormat.expWidth
  let fracWidth ← natural ``FloatFormat.fracWidth
  let isIEEE ← Tactic.KernelReadBack.kernelWhnf (mkApp (Lean.mkConst ``FloatFormat.isIEEE) format)
    "the format of the arithmetic"
  unless isIEEE.isConstOf ``Bool.true do
    throwErrorAt stx "the format `{name}` is not an IEEE format (`FloatFormat.isIEEE` is false \
      for it). The float arithmetic of `cega` takes IEEE formats only; \
      `FloatFormat.ieee {expWidth} {fracWidth}` has the same widths"
  return .float name expWidth fracWidth

/-- The arithmetic that `text` names: `exact`, `binary(p := N, emax := M)`, or the text of a
format term for `elabFormat`. This is the language of the option `cega.arithmetic` and of a
string value of `(arith := F)`. Errors are reported at `ref`. -/
def parseArithmeticText (ref : Syntax) (text : String) : TermElabM Arithmetic := do
  let name := trimmed text
  if name == "exact" then
    return .exact
  if let some (p, emax) := precisionForm? name then
    let some (expWidth, fracWidth) := widthsOfPrecision? p emax
      | throwErrorAt ref "`{name}` is not an IEEE binary format: the precision `p` is at least \
          2, and `emax + 1` is a power of two that is at least 2, as in \
          `binary(p := 53, emax := 1023)` for binary64"
    return .float name expWidth fracWidth
  match Parser.runParserCategory (← getEnv) `term name with
  | .ok stx => withRef ref <| elabFormat (stx.setInfo (SourceInfo.fromRef ref)) name
  | .error _ =>
      throwErrorAt ref "`{name}` is not an arithmetic of `cega`; expected `\"exact\"` or a \
        FloatLib binary format: {formatExamples}"

/-- The arithmetic of the value `value` of an item `(arith := value)`: a format term, or a
string literal with the text that `parseArithmeticText` reads. -/
def parseArithmeticItem (value : Syntax) : TermElabM Arithmetic := do
  if let some text := value.isStrLit? then
    return ← parseArithmeticText value text
  let written := trimmed (value.reprint.getD "")
  let name ← if written.isEmpty then
      pure (toString (← PrettyPrinter.ppCategory `term value))
    else pure written
  elabFormat value name

/-- The value of the item `(arith := F)` of the configuration group `optConfig`, if it has one,
and the group without that item, for the parsers of the precision options. -/
def splitArithmeticItem {m : Type → Type} [Monad m] [MonadError m] (optConfig : Syntax) :
    m (Option Syntax × Syntax) := do
  let mut value? : Option Syntax := none
  let mut others : Array Syntax := #[]
  for item in CAS.Command.configItems 16 optConfig do
    match CAS.Command.valueConfigItem? item with
    | some (`arith, value) =>
        if value?.isSome then
          throwErrorAt item "the arithmetic is given twice; keep one `(arith := F)`"
        value? := some value
    | _ => others := others.push item
  return (value?, mkNullNode others)

/-- Whether the option `cega.arithmetic` asks for exact arithmetic, by its text. -/
def exactByOption {m : Type → Type} [Monad m] [MonadOptions m] : m Bool :=
  return trimmed (cega.arithmetic.get (← getOptions)) == "exact"

/-- The text of the item that asks for exact arithmetic, with a leading space, where the option
`cega.arithmetic` of the section is a float format, and nothing elsewhere. A call of the exact
routes that a message prints with it runs in exact arithmetic wherever it is pasted. -/
def exactItemText {m : Type → Type} [Monad m] [MonadOptions m] : m String :=
  return if ← exactByOption then "" else " (arith := \"exact\")"

/-! ## The arithmetic of one call -/

/-- The format of `[use_floats]` when neither the call nor the section names one. -/
def defaultFormat : String := "binary64"

/-- What one `cega` call says about its arithmetic. -/
structure ArithmeticRequest where
  /-- The flag `use_floats := b`, where `use_floats` alone is `true`; `none` without the flag. -/
  floats? : Option Bool := none
  /-- The value of the item `(arith := F)`. -/
  format? : Option Syntax := none

/-- The arithmetic of a call: the format of its item `(arith := F)`; otherwise exact for
`use_floats := false`; otherwise the arithmetic of the option `cega.arithmetic`, with
`defaultFormat` in place of exact for `use_floats := true`. A flag and an item that contradict
each other are refused. A call without flag and item in a section without the option resolves to
exact arithmetic with no elaboration. -/
def ArithmeticRequest.resolve (request : ArithmeticRequest) : TermElabM Arithmetic := do
  if let some value := request.format? then
    let arithmetic ← parseArithmeticItem value
    match arithmetic, request.floats? with
    | .float name .., some false =>
        throwErrorAt value "`use_floats := false` asks for exact arithmetic and \
          `(arith := {name})` for a float format; remove one of them"
    | .exact, some true =>
        throwErrorAt value "`use_floats := true` asks for a float format and \
          `(arith := \"exact\")` for exact arithmetic; remove one of them"
    | _, _ => return arithmetic
  if request.floats? == some false then
    return .exact
  let inherited ←
    try
      parseArithmeticText (← getRef) (cega.arithmetic.get (← getOptions))
    catch error =>
      throwError "the option `cega.arithmetic` does not name an arithmetic:\
        {indentD error.toMessageData}"
  if request.floats? == some true && !inherited.isFloat then
    return ← parseArithmeticText (← getRef) defaultFormat
  return inherited

/-! ## Messages -/

/-- The standard interchange formats of FloatLib's catalog, narrowest first. -/
def standardFormats : List String := ["binary16", "binary32", "binary64", "binary128", "binary256"]

/-- The narrowest standard format with at least the exponent and fraction bits of a float
arithmetic and more of one of them, read from FloatLib's catalog; `none` for exact arithmetic
and beyond the catalog. -/
def Arithmetic.wider? : Arithmetic → TermElabM (Option String)
  | .exact => return none
  | .float _ expWidth fracWidth => do
      for name in standardFormats do
        -- A name that the catalog does not have is skipped.
        let standard ← try parseArithmeticText (← getRef) name catch _ => pure .exact
        if let .float _ e f := standard then
          if expWidth ≤ e ∧ fracWidth ≤ f ∧ (expWidth < e ∨ fracWidth < f) then
            return some name
      return none

/-- The text of the configuration item that asks for an arithmetic, with a leading space:
` (arith := binary64)`, with the name in quotes when it is not a term, and nothing for exact
arithmetic. -/
def Arithmetic.itemText : Arithmetic → String
  | .exact => ""
  | .float name .. =>
      if (precisionForm? name).isSome then s!" (arith := \"{name}\")" else s!" (arith := {name})"

/-! ## Why a float query has no result -/

/-- Why a float query has no result: the first obstruction of FloatLib's diagnosis
(`Expr.diagnose`) of the evaluation that the query runs, as `CAS.CEGA.Elaboration` reads it back
from the kernel. An operation is named by its constructor in FloatLib's expressions, such as
`UnaryOp.log` or `BinaryOp.div`, or `Expr.const`, `Expr.var` and `Expr.call` for a constant, a
variable and a registered call, with the index of the variable or of the call. -/
inductive FloatFailure where
  /-- A bound of the box has no enclosure in the format, which the diagnosis reports as a variable
  without an interval. -/
  | box
  /-- FloatLib has no enclosure of `operation` on its operands. `inputs` are the rational ends of
  the enclosures of the first three operands, in order. -/
  | rejected (operation : Name) (index : Nat) (inputs : List (ℚ × ℚ))
  /-- An end of an operand enclosure of `operation` is not a finite number of the format. -/
  | undecodable (operation : Name) (index : Nat)

open FloatLib.Numerics in
/-- The words for the operation `operation` of FloatLib's expressions, with the index `index` of
a variable or a registered call. The calls are FloatLib's standard extensions, which SymLean's
translation into FloatLib's expressions uses: the call `0` is `π`, the call `1` a real power and
the call `2` the constant `e`. -/
def operationWords : Name → Nat → String
  | ``Interval.Expr.const, _ => "a constant"
  | ``Interval.Expr.var, index => s!"the coordinate {index}"
  | ``Interval.Expr.call, 0 => "π"
  | ``Interval.Expr.call, 1 => "a real power"
  | ``Interval.Expr.call, 2 => "e"
  | ``Interval.Expr.call, index => s!"the registered function {index}"
  | ``Interval.UnaryOp.neg, _ => "a negation"
  | ``Interval.UnaryOp.abs, _ => "an absolute value"
  | ``Interval.UnaryOp.inv, _ => "a reciprocal"
  | ``Interval.UnaryOp.pow, _ => "a power"
  | ``Interval.UnaryOp.exp, _ => "an exponential"
  | ``Interval.UnaryOp.log, _ => "a logarithm"
  | ``Interval.UnaryOp.sin, _ => "a sine"
  | ``Interval.UnaryOp.cos, _ => "a cosine"
  | ``Interval.UnaryOp.tan, _ => "a tangent"
  | ``Interval.UnaryOp.asin, _ => "an arcsine"
  | ``Interval.UnaryOp.acos, _ => "an arccosine"
  | ``Interval.UnaryOp.atan, _ => "an arctangent"
  | ``Interval.UnaryOp.sinh, _ => "a hyperbolic sine"
  | ``Interval.UnaryOp.cosh, _ => "a hyperbolic cosine"
  | ``Interval.UnaryOp.tanh, _ => "a hyperbolic tangent"
  | ``Interval.UnaryOp.sqrt, _ => "a square root"
  | ``Interval.BinaryOp.add, _ => "a sum"
  | ``Interval.BinaryOp.sub, _ => "a difference"
  | ``Interval.BinaryOp.mul, _ => "a product"
  | ``Interval.BinaryOp.div, _ => "a quotient"
  | ``Interval.BinaryOp.min, _ => "a minimum"
  | ``Interval.BinaryOp.max, _ => "a maximum"
  | ``Interval.TernaryOp.fma, _ => "a fused multiply-add"
  | operation, _ => s!"the operation `{operation}`"

namespace FloatFailure

open FloatLib.Numerics in
/-- The divisor interval of a quotient or a reciprocal that FloatLib could not enclose. -/
def divisor? : FloatFailure → Option (ℚ × ℚ)
  | .rejected ``Interval.BinaryOp.div _ [_, divisor]
  | .rejected ``Interval.UnaryOp.inv _ [divisor] => some divisor
  | _ => none

/-- Whether FloatLib could not enclose a quotient or a reciprocal because its divisor interval
contains zero. A subdivision of the box may separate the divisor from zero. -/
def divisorContainsZero (failure : FloatFailure) : Bool :=
  failure.divisor?.any fun (lo, hi) ↦ lo ≤ 0 ∧ 0 ≤ hi

open FloatLib.Numerics in
/-- The words for an operand interval outside the domain of the operation that FloatLib could not
enclose: a divisor interval that contains zero, an argument of a logarithm or a base of a real
power that is not positive, an argument of a square root with negative numbers, or an argument of
an arcsine or an arccosine outside `[-1, 1]`; `none` for every other failure. A wider format does
not move an interval into the domain. -/
def outsideDomain? (failure : FloatFailure) : Option String :=
  if failure.divisorContainsZero then some "a divisor interval contains zero"
  else match failure with
    | .rejected ``Interval.UnaryOp.log _ ((lo, _) :: _) =>
        if lo ≤ 0 then some "a logarithm has an argument interval that is not positive" else none
    | .rejected ``Interval.Expr.call 1 ((lo, _) :: _) =>
        if lo ≤ 0 then some "a real power has a base interval that is not positive" else none
    | .rejected ``Interval.UnaryOp.sqrt _ ((lo, _) :: _) =>
        if lo < 0 then some "a square root has an argument interval with negative numbers"
        else none
    | .rejected operation index [(lo, hi)] =>
        if operation ∈ [``Interval.UnaryOp.asin, ``Interval.UnaryOp.acos] ∧
            (lo < -1 ∨ 1 < hi) then
          some s!"{operationWords operation index} has an argument interval outside [-1, 1]"
        else none
    | _ => none

end FloatFailure

open FloatLib.Numerics in
/-- Why a float query in the format `name` has no result, from FloatLib's diagnosis `failure`: an
operand interval outside the domain of its operation (`FloatFailure.outsideDomain?`), a bound of
the box or an end of the enclosure of an operation beyond the largest finite number of the format,
or a tangent, an arcsine or an arccosine that FloatLib could not enclose on its argument interval.
On operands in its domain, every other operation of FloatLib's float backend fails only when its
enclosure, rounded outward, has an end beyond the largest finite number, so the message names an
overflow. -/
def floatFailure (name : String) (failure : FloatFailure) : String :=
  match failure.outsideDomain?, failure with
  | some words, _ => s!"{words} in {name} arithmetic"
  | none, .box => s!"a bound of the box is beyond the largest finite {name} number (overflow)"
  | none, .undecodable operation index =>
      s!"an end of an operand of {operationWords operation index} is not a finite {name} number"
  | none, .rejected operation index _ =>
      if operation ∈ [``Interval.UnaryOp.tan, ``Interval.UnaryOp.asin, ``Interval.UnaryOp.acos]
      then
        s!"FloatLib has no {name} enclosure of {operationWords operation index} on its argument \
          interval"
      else
        s!"the enclosure of {operationWords operation index} has an end beyond the largest finite \
          {name} number (overflow)"

/-- The calls to try when a float format does not prove a goal: a wider format, when the
catalog has one and `wider` holds, and exact arithmetic, written `exactCall`. A caller sets
`wider` to `false` for a failure that a wider format does not remove, such as an interval outside
the domain of a function (`FloatFailure.outsideDomain?`). -/
def Arithmetic.remedy (arithmetic : Arithmetic)
    (exactCall : String := "cega [use_floats := false]") (wider : Bool := true) :
    TermElabM MessageData := do
  let format? ← if wider then arithmetic.wider? else pure none
  match format? with
  | some format =>
      return m!"A wider format, as in `(arith := {format})`, or exact arithmetic, \
        `{exactCall}`, may prove it."
  | none => return m!"Exact arithmetic, `{exactCall}`, may prove it."

/-- A line for the message of a route whose enclosure did not give the goal: in a float
arithmetic, the format and the calls to try (`Arithmetic.remedy`); nothing in exact
arithmetic. -/
def arithmeticNote (exactCall : String := "cega [use_floats := false]") :
    TermElabM MessageData := do
  let arithmetic ← activeArithmetic
  let .float name .. := arithmetic
    | return m!""
  return m!"\nThe enclosure was computed in {name} arithmetic. {← arithmetic.remedy exactCall}"

end CAS.CEGA.Elaboration

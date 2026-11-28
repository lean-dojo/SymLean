/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.CEGA.Elaboration
public import CAS.CEGA.FloatQuery
public import CAS.CEGA.Integration
public meta import CAS.CEGA.Integration
public import CAS.CEGA.ExpressionSyntax
public meta import CAS.CEGA.ExpressionSyntax
public import CAS.CEGA.Query
public import CAS.ExactTactic
public import CAS.Tactic.BoxInequality
public meta import CAS.Tactic.BoxInequality
public import CAS.Tactic.CEGA
public import CAS.Continuum.Interval.Inclusion.Elementary
public meta import FloatLib.Tactic.FloatDecide
public meta import FloatLib.Tactic.Interval
public meta import FloatLib.Tactic.KernelCheck
import Mathlib.Tactic.Inclusion.Core.Elab
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Certified Enclosures, Guarantees, and Approximations

`cega` proves statements about real expressions on finite boxes with checked rational
interval arithmetic, and closed statements about floats by evaluation in the kernel. The main
forms are:

* Bare `cega` first projects a checked carrier (a certificate, a `CertificateRoute`, or a
  registered attempt type) found in the local context or in the goal, through its soundness
  theorem (`CAS.Tactic.CEGA`). A closed decidable statement about the values of a float format,
  such as `(1.5 : Binary64) + 2.25 = 3.75`, is decided in the kernel as `float_decide` decides it
  (`FloatLib.Tactic.KernelCheck.prove`), after FloatLib's kernel rules have rewritten its float
  operations. A goal about one interval integral `∫ x in a..b, f x` with rational limits and a
  closed elementary integrand is proved by a checked batch quadrature
  (`CAS.CEGA.Integration`): Simpson panels with a fourth-derivative remainder where the domain
  checker certifies the integrand and its first four derivatives on `[a, b]`, and range panels,
  which need only continuity, otherwise or when Simpson panels fall short; the panel count doubles
  until the goal holds, up to `cega.maxIntegrationPanels`, or `(panels := n)` sets it. A certificate
  goal (`EnclosedOn f s lo hi`, `BoundOn f s c`, `ApproxOn f g s ε`, `ResidualBound r s ε`) whose
  domain `s` is a coordinate box is unfolded to an ordinary goal on the coordinates of its
  point. An ordinary inequality on real variables bounded by rational literal hypotheses, or a
  conjunction of such inequalities, is proved on the box those hypotheses describe by FloatLib's
  check or else by the checked query (`CAS.Tactic.BoxInequality`). A real or nonnegative real
  inequality that this query does not prove, or cannot read, such as a bound on a finite sum, a norm
  or a matrix product, goes to FloatLib's `interval`, and so does a bound over a whole domain
  (`∀ u : ℝ, …`, `∀ x ∈ Set.Icc lo hi, …`, `∀ z : ℂ, ‖z‖ = 1 → …`). A goal without free variables
  that no route proves, such as a conjunction, a negation or an equality of real constants, is
  evaluated with `dyadic_interval [cega_real, prec := n]`
  (`CAS.Continuum.Interval.Inclusion.Elementary`), with `n` from `(prec := n)`, about `3.3 d + 8`
  for `(digits := d)`, and `32` otherwise. If the semantic routes refuse a closed decidable
  proposition that is not about floats, bare `cega` tries a kernel certificate check. When the box
  query does not prove the bound, the box route subdivides the box, by default to depth two;
  `cega (prec := n) (depth := n)` sets the precision and that depth, and gives `interval` the
  endpoint bits `n` (about `3.3 d + 8` for `(digits := d)`) and the subdivision depth `n`, which are
  otherwise FloatLib's defaults.
* `cega using h` projects the one carrier `h`. The proof keeps every hypothesis and axiom that
  the proof of `h` uses, a native-evaluation axiom included, and projection does not check
  where the data of `h` came from; `cega.nativeCertificates` governs only new checks.
* `cega [fast]` first decides a closed statement about floats with `float_decide` in the kernel,
  then tries a closed finite decidable certificate, then the computable natural interval
  evaluator. These numerical checks use native evaluation when
  `cega.nativeCertificates` is true, and trust Lean's compiler and runtime; their generated
  axioms have names containing `_native.cegaFast.ax`. The option is false by default, and then
  `cega [fast]` is bare `cega`. Failed native attempts restore the proof state and environment
  before kernel CEGA runs. The ordinary symbolic proofs and semantic planner remain kernel
  checked.
* `cega [use_floats]` runs bare `cega` with the enclosures of its box queries computed in IEEE
  floating-point arithmetic, binary64 or the format of `(arith := F)`, instead of exact
  rationals (`CAS.CEGA.FloatQuery`, `CAS.CEGA.Arithmetic`); `set_option cega.arithmetic` sets
  the arithmetic of a section, a lakefile that of a whole build (`weak.cega.arithmetic` in its
  Lean options), and `cega (arith := F) [enclose …] e` that of an explicit query.
  The carrier route computes nothing and `float_decide` evaluates the floats that the statement
  names, so both remain available. The quadrature of an integral, `interval` and `dyadic_interval`
  compute with exact numbers, so they are not run and say so, and the kernel certificate of a
  closed decidable proposition is not tried on a goal that the float query read. A float query
  that does not prove its goal is a failure of the tactic, with the format and the reason; no
  route computes with rationals in its place.
* `cega [enclose x in [a, b], …] e` runs the query on `e` over the stated rational box and
  proves the projection the goal needs. The goal is a certificate proposition
  (`EnclosedOn f s lo hi`, `BoundOn f s c`, `ApproxOn f g s ε`) whose domain `s` lies in the box,
  or an ordinary inequality on the box's variables; an enclosure, an upper bound, an absolute
  bound for `BoundOn (fun x ↦ |f x|) s c` or `|f x| ≤ c`, or a midpoint approximation is
  certified accordingly. A configuration such as `(prec := 40)` sets the precision policy, and
  `(depth := 3)` computes the enclosure after three levels of checked box refinement, whichever
  of these the goal needs.

For example, `x * (1 - x) ≤ 1 / 4` under `0 ≤ x` and `x ≤ 1` is closed by bare `cega` and by
`cega [enclose x in [0, 1]] (x * (1 - x))`. A hypothesis `|x| ≤ r` or `|x| < r` gives the box
`[-r, r]`, and an applied term such as `f x` is a coordinate when hypotheses bound it. A closed
inequality such as `Real.sqrt 2 ≤ 2` uses the box with no coordinates, written
`cega [enclose] √(2 : ℝ)` in explicit form. A nonrational closed endpoint is compared by the same
checked evaluator, so `Real.exp x ≤ Real.exp 3` is proved on `x ∈ Set.Icc 0 1`.

A query certifies the value of a total expression on a closed box. Analytic domain conditions,
such as those needed for differentiation, are separate obligations. Strict hypotheses are
weakened to closed bounds, so a strict goal needs a strict gap between the requested bound and
the certified endpoint.

Importing `CAS.CEGA` registers `boxRoute` with `@[cas_route box]`, and bare `cas` calls it from
its `box` stage (`CAS/ExactTactic.lean`) when its earlier stages, its Mathlib arithmetic script
among them, have not closed the goal. The numerical `#cas` commands come with `CAS`, and `cega?`
reporting with `CAS.Reporting`.

## Main definitions

* `closeBare`: the routes of bare `cega`, in their order, with a refusal that leads with the
  reason of the route that applies to the goal.
* `closeEncloseQuery`: the explicit query `cega [enclose x in [a, b]] e`.
* `closeBoxQuery`: run a checked box query and close a certificate goal, or an ordinary
  inequality on the box's variables, with its result.
* `closeClosedByInclusion`, `inclusionQuery`: `dyadic_interval` with the `cega_real` ranges on a
  goal without free variables.
* `BareRoute`: the route by which bare `cega` closed a goal and, except for a projected carrier,
  the call that replays it.
* `bareDepth?`: the depth of the item `(depth := n)` of a bare call, which `interval` receives.
* `boxRoute`: the box route as a route of bare `cas`.

## Implementation notes

Bare `cega` tries its routes in a fixed order (`closeBare`): the projection of a carrier
(`CAS/Tactic/CEGA.lean`), `float_decide` on a closed statement about floats, the quadrature of
`CAS/CEGA/Integration.lean`, a certificate goal on a coordinate box and then an ordinary
inequality (`CAS/Tactic/BoxInequality.lean`), FloatLib's `interval` on a real inequality, and for
a closed goal `dyadic_interval` with the ranges of
`CAS/Continuum/Interval/Inclusion/Elementary.lean`. Each route first reads the shape of the goal,
from its syntax and types only, and a route whose shape does not fit is not run; the refusal
leads with the reason of the first route whose shape fits. When all of them refuse a closed
decidable goal that is not about floats, we evaluate its decision in the kernel
(`decideClosedCertificate` in `CAS/CEGA/Elaboration.lean`). A statement about floats is not
evaluated a second time: `float_decide` has decided it, with the kernel rules, and the
certificate would decide it without them. Two routes come from FloatLib: `float_decide` is
`FloatLib.Tactic.KernelCheck.prove`, run with the heartbeats the declaration has left, and the
interval route runs the `interval` call it suggests, so a faster FloatLib definition or a new
kernel rule reaches both with no change here. The other routes compute no enclosure
themselves: `CAS/CEGA/Elaboration.lean` quotes a query, bounds its size and has the kernel
evaluate it, and the planner that the kernel runs, in `CAS/CEGA/Query.lean` (finite charts,
monotonicity faces, the centered mean-value form, checked bisection), carries the references to
the classical interval methods. What we add is the order of the routes, the reading of the goal
and the transport of a checked theorem to the goal as it is stated.

We run every form except native `cega [fast]` as a kernel-only route
(`Tactic.ProofCarrier.withKernelOnlyAxioms`): its proof may use no axiom beyond `propext`,
`Classical.choice` and `Quot.sound` that the goal, the hypotheses it uses, or an explicit carrier
does not already use, and a proof that does is rejected with the axiom's name. The float_decide
route is kernel-only under native `cega [fast]` as well. Natively checked theorems are added
outside Lean's auxiliary-lemma cache, so a later kernel route for the same statement, in the same
declaration or another, cannot receive one. `CAS.Examples.CEGA.Trust` tests this contract on the
kernel routes.

A goal that states its bounds with closed numerals, such as `EnclosedOn f s (-1) 1` or
`x * (1 - x) ≤ 1 / 4`, is first tried in bare `cega` by FloatLib's check, which refutes the negation
of the bounds on a subdivision of the box (`CAS.Tactic.BoxInequality`). When that check falls short,
and first in the explicit form, the stated-bound route tries the goal: the kernel checks one theorem
that compares the interval of the query with the stated numbers
(`CEGA.Elaboration.checkStatedBounds`), running the planner while it checks, so the search in the
elaborator and the read-back of the endpoints are skipped; the checked theorem is transported to
the goal like a query result. When the kernel rejects the check, bare `cega` checks the
subdivided query the same way, where it would subdivide, and refuses the goal with the values
that its queries certify, read back in one kernel evaluation. The explicit form then runs the
search, whose diagnostics and refusals are the tactic's, so a goal it refuses costs the rejected
check as well. A query that the search has memoized runs the search.

On a certificate goal, the generated proof is accepted when it matches the goal after unfolding;
otherwise it is transported by inclusion of the domains, equality of the functions on the goal's
domain, and endpoint arithmetic, and as a last step the certificate itself is projected by
`Tactic.Certificate.closeUsingCertificate`. When both fail, the error shows both causes,
including the inclusion or endpoint inequality that transport could not prove. Planner traces
and rendered metadata are never proof carriers. Certificate code calls the same checked queries
directly through `CAS.CEGA.Query`.
-/

public meta section

namespace CAS.CEGA

open Lean Elab Tactic Meta
open CAS.CEGA.Elaboration

/-- Compare one applied semantic relation without unfolding the relation itself. -/
private def appliedRelationDefEq?
    (lhs rhs : Lean.Expr) : TacticM Bool := do
  let lhs := lhs.consumeMData
  let rhs := rhs.consumeMData
  unless lhs.getAppFn == rhs.getAppFn do
    return false
  let lhsArgs := lhs.getAppArgs
  let rhsArgs := rhs.getAppArgs
  unless lhsArgs.size = rhsArgs.size do
    return false
  for (lhsArg, rhsArg) in lhsArgs.zip rhsArgs do
    let equivalent ← withTransparency .all <| Elaboration.DefEq.agree lhsArg rhsArg
    unless equivalent do
      return false
  return true

/--
Prove that an ordinary theorem domain lies inside the exact box certified by a query.

The generated source domain unfolds to finitely many rational coordinate inequalities.
`fin_cases` exposes those coordinates, after which `simp_all` and `norm_num` can use the
set-builder hypotheses of the theorem statement. It is used when a certificate goal's
domain is not definitionally the query box.
-/
private def inferDomainSubsetProof
    (targetDomain sourceDomain : Lean.Expr) : TacticM Lean.Expr := do
  -- A named domain unfolds to its set-builder form `Set.ofPred _`, whose membership `simp_all`
  -- reads with `Set.mem_ofPred_eq`.
  let targetDomain ← withTransparency .all <| whnf targetDomain
  let expected ← mkAppM ``Set.Subset #[targetDomain, sourceDomain]
  let proof ← mkFreshExprMVar expected
  let tactic ← `(tactic|
    (intro point membership coordinate; fin_cases coordinate) <;>
      simp_all [CAS.Continuum.RationalInterval.MemReal,
        CAS.Continuum.RationalInterval.ofBounds])
  let remaining ← proof.mvarId!.withContext do
    evalTacticAt tactic proof.mvarId!
  let remaining ← remaining.flatMapM fun goal ↦ goal.withContext do
    evalTacticAt (← `(tactic| norm_num)) goal
  unless remaining.isEmpty do
    let targets ← remaining.mapM fun goal ↦
      goal.withContext do Meta.ppGoal goal
    throwError
      "the theorem domain was not proved to lie inside the certified rational box\
       \n{String.intercalate "\n" (targets.map (·.pretty))}"
  Tactic.ProofCarrier.checkCompletedProof "CEGA theorem-domain inclusion" proof

/-- Use reflexivity when both domains coincide, or prove the needed box inclusion. -/
private def domainSubsetProof
    (targetDomain sourceDomain : Lean.Expr) : TacticM Lean.Expr := do
  if ← withTransparency .all <| Elaboration.DefEq.agree targetDomain sourceDomain then
    mkAppM ``Set.Subset.refl #[sourceDomain]
  else
    inferDomainSubsetProof targetDomain sourceDomain

/-- Use definitional equality before invoking the reflected-function normalizer. -/
private def functionEqOnProof
    (targetFn sourceFn domain : Lean.Expr) : TacticM Lean.Expr := do
  if ← Tactic.ProofCarrier.isDefEqReadOnly targetFn sourceFn then
    mkAppM ``Set.eqOn_refl #[sourceFn, domain]
  else
    Tactic.Certificate.inferNormalizedEqOnProof targetFn sourceFn domain

/-- Transport a generated enclosure directly to its ordinary theorem presentation. -/
private def assignTransportedEnclosureProof?
    (proof : Lean.Expr) (target : Lean.Expr) : TacticM Bool :=
  Tactic.ProofCarrier.restoringStateOnFalse do
    let source := (← inferType proof).consumeMData
    let target := target.consumeMData
    unless source.getAppFn.isConstOf ``Certificate.EnclosedOn ∧
        target.getAppFn.isConstOf ``Certificate.EnclosedOn do
      return false
    let sourceArgs := source.getAppArgs
    let targetArgs := target.getAppArgs
    unless sourceArgs.size ≥ 4 ∧ targetArgs.size ≥ 4 do
      return false
    let sourceFn := sourceArgs[sourceArgs.size - 4]!
    let sourceDomain := sourceArgs[sourceArgs.size - 3]!
    let sourceLower := sourceArgs[sourceArgs.size - 2]!
    let sourceUpper := sourceArgs[sourceArgs.size - 1]!
    let targetFn := targetArgs[targetArgs.size - 4]!
    let targetDomain := targetArgs[targetArgs.size - 3]!
    let targetLower := targetArgs[targetArgs.size - 2]!
    let targetUpper := targetArgs[targetArgs.size - 1]!
    let hsub ← domainSubsetProof targetDomain sourceDomain
    let hfn ← functionEqOnProof targetFn sourceFn targetDomain
    let lowerGoal ← mkAppM ``LE.le #[targetLower, sourceLower]
    let upperGoal ← mkAppM ``LE.le #[sourceUpper, targetUpper]
    let hlower ←
      Tactic.Certificate.inferArithmeticProof "CEGA enclosure lower endpoint" lowerGoal
    let hupper ←
      Tactic.Certificate.inferArithmeticProof "CEGA enclosure upper endpoint" upperGoal
    let transported ←
      mkAppM ``Certificate.enclosedOn_congr #[proof, hsub, hfn]
    let widened ← mkAppM ``Certificate.enclosedOn_mono #[transported, hlower, hupper]
    Tactic.ProofCarrier.assignExactProof "CEGA enclosure transport" widened

/-- Transport a generated upper bound directly to its ordinary theorem presentation. -/
private def assignTransportedBoundProof?
    (proof : Lean.Expr) (target : Lean.Expr) : TacticM Bool :=
  Tactic.ProofCarrier.restoringStateOnFalse do
    let source := (← inferType proof).consumeMData
    let target := target.consumeMData
    unless source.getAppFn.isConstOf ``Certificate.BoundOn ∧
        target.getAppFn.isConstOf ``Certificate.BoundOn do
      return false
    let sourceArgs := source.getAppArgs
    let targetArgs := target.getAppArgs
    unless sourceArgs.size ≥ 3 ∧ targetArgs.size ≥ 3 do
      return false
    let sourceFn := sourceArgs[sourceArgs.size - 3]!
    let sourceDomain := sourceArgs[sourceArgs.size - 2]!
    let sourceUpper := sourceArgs[sourceArgs.size - 1]!
    let targetFn := targetArgs[targetArgs.size - 3]!
    let targetDomain := targetArgs[targetArgs.size - 2]!
    let targetUpper := targetArgs[targetArgs.size - 1]!
    let hsub ← domainSubsetProof targetDomain sourceDomain
    let hfn ← functionEqOnProof targetFn sourceFn targetDomain
    let upperGoal ← mkAppM ``LE.le #[sourceUpper, targetUpper]
    let hupper ←
      Tactic.Certificate.inferArithmeticProof "CEGA upper-bound endpoint" upperGoal
    let transported ←
      mkAppM ``Certificate.boundOn_congr #[proof, hsub, hfn]
    let widened ← mkAppM ``Certificate.boundOn_mono #[transported, hupper]
    Tactic.ProofCarrier.assignExactProof "CEGA upper-bound transport" widened

/-- Transport a generated midpoint approximation to its ordinary theorem presentation. -/
private def assignTransportedApproxProof?
    (proof : Lean.Expr) (target : Lean.Expr) : TacticM Bool :=
  Tactic.ProofCarrier.restoringStateOnFalse do
    let source := (← inferType proof).consumeMData
    let target := target.consumeMData
    unless source.getAppFn.isConstOf ``Certificate.ApproxOn ∧
        target.getAppFn.isConstOf ``Certificate.ApproxOn do
      return false
    let sourceArgs := source.getAppArgs
    let targetArgs := target.getAppArgs
    unless sourceArgs.size ≥ 4 ∧ targetArgs.size ≥ 4 do
      return false
    let sourceFn := sourceArgs[sourceArgs.size - 4]!
    let sourceReference := sourceArgs[sourceArgs.size - 3]!
    let sourceDomain := sourceArgs[sourceArgs.size - 2]!
    let sourceError := sourceArgs[sourceArgs.size - 1]!
    let targetFn := targetArgs[targetArgs.size - 4]!
    let targetReference := targetArgs[targetArgs.size - 3]!
    let targetDomain := targetArgs[targetArgs.size - 2]!
    let targetError := targetArgs[targetArgs.size - 1]!
    let hsub ← domainSubsetProof targetDomain sourceDomain
    let hfn ← functionEqOnProof targetFn sourceFn targetDomain
    let href ← functionEqOnProof targetReference sourceReference targetDomain
    let errorGoal ← mkAppM ``LE.le #[sourceError, targetError]
    let herror ←
      Tactic.Certificate.inferArithmeticProof "CEGA approximation error" errorGoal
    let transported ←
      mkAppM ``Certificate.approxOn_congr #[proof, hsub, hfn, href]
    let widened ← mkAppM ``Certificate.approxOn_mono_error #[transported, herror]
    Tactic.ProofCarrier.assignExactProof "CEGA approximation transport" widened

/--
Assign a kernel-checked query theorem `proof`, the one validated by `runBoxQuery` or by
`checkStatedBounds`, when its semantic proposition matches the theorem goal after unfolding user
definitions. Otherwise transport it to the goal by domain inclusion, function equality on the
domain, and endpoint arithmetic (`assignTransportedEnclosureProof?`,
`assignTransportedBoundProof?`, `assignTransportedApproxProof?`, by query mode).

The raw query syntax has no named boxes or functions, so the generated
proposition contains their quoted lambda forms. The argument-wise comparison
with the goal runs at all transparency, as does the comparison of the domains
in the transport (`domainSubsetProof`).
-/
private def assignValidatedBoxProof?
    (mode : BoxQueryMode) (proof : Lean.Expr) : TacticM Bool := do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let proof ← instantiateMVars proof
  let proposition ← instantiateMVars (← inferType proof)
  if ← appliedRelationDefEq? proposition target then
    return ← Tactic.ProofCarrier.assignExactProof "CEGA generated query" proof
  match mode with
  | .enclose => assignTransportedEnclosureProof? proof target
  | .bound | .absBound => assignTransportedBoundProof? proof target
  | .approx => assignTransportedApproxProof? proof target

/-- Whether a goal is one of the certificate propositions a box query proves directly. -/
private def isCertificateTarget (target : Expr) : Bool :=
  let head := target.consumeMData.getAppFn.consumeMData
  head.isConstOf ``Certificate.EnclosedOn ∨ head.isConstOf ``Certificate.BoundOn ∨
    head.isConstOf ``Certificate.ApproxOn

/-- How an explicit query asks for exact arithmetic in a section whose option
`cega.arithmetic` is a float format, for the messages of a float query that falls short. -/
private def explicitExactCall : String := "(arith := \"exact\")"

/-- Run a checked finite-box query and close the current matching semantic goal, or the
current ordinary inequality on the box's variables.

On a certificate goal (`EnclosedOn`, `BoundOn`, `ApproxOn`) the generated proof is first
compared with the goal up to unfolding. Failing that, it is transported by domain inclusion,
function equality on the domain, and endpoint arithmetic. If certificate projection
also fails, the diagnostic includes both its refusal and the transport error.

On an ordinary inequality (after introducing leading binders, so that `∀ x ∈ Set.Icc a b, …`
is accepted) the coordinates of the query must be local real variables whose hypotheses place
them inside the stated box, and the certificate is transported by
`Tactic.BoxInequality.closeWithExplicitQuery`. Any other goal is refused with its head symbol
and the shapes the query proves. -/
def closeBoxQuery
    (ref : Syntax) (mode : BoxQueryMode) (method : EnclosureMethod)
    (precision : Continuum.RationalInterval.Precision)
    (bindingSyntax : Array Syntax) (expression : Syntax) :
    TacticM BoxQueryResult :=
  Tactic.ProofCarrier.preservingStateOnFailure do
    let bindings ← parseBindings bindingSyntax
    let coordinates := bindings.map BoxBinding.coordinate
    let reified ← parseExpression expression coordinates
    let box := bindings.map BoxBinding.interval
    Tactic.BoxInequality.introduceBinders
    let target ← withMainContext do instantiateMVars (← getMainTarget)
    let ordinary? ←
      if isCertificateTarget target then pure none
      else withMainContext do Tactic.BoxInequality.recognize? target
    unless isCertificateTarget target ∨ ordinary?.isSome do
      throwErrorAt ref
        "cega [enclose ...] proves a certificate goal `EnclosedOn f s lo hi`, \
         `BoundOn f s c`, or `ApproxOn f g s ε` whose domain lies in the stated box, or an \
         ordinary inequality on the box's variables ({Tactic.BoxInequality.supportedShapes}). \
         This goal has {← Tactic.BoxInequality.describeHead target}."
    let some result ← liftM <| runBoxQuery mode method precision box reified.expr
      | throwErrorAt ref (← queryFailureMessage method precision box reified.expr
          (exactCall := explicitExactCall))
    match ordinary? with
    | some _ =>
        try
          Tactic.BoxInequality.closeWithExplicitQuery "cega" bindings result precision
        catch error =>
          throwErrorAt ref
            "cega generated a checked {mode.certificateName} certificate for the stated query, but \
             could not transport it to this ordinary inequality.\n{error.toMessageData}\
             {← arithmeticNote explicitExactCall}"
    | none =>
        let transport : Except Exception Bool ← try
          pure (.ok (← Tactic.ProofCarrier.preservingStateOnFailure
            (assignValidatedBoxProof? mode result.proof)))
        catch error =>
          pure (.error error)
        unless transport matches .ok true do
          try
            Tactic.Certificate.closeUsingCertificate result.certificate
          catch error =>
            let detail := match transport with
              | .error cause => m!"Transport:{indentD cause.toMessageData}"
              | .ok _ => m!"Transport: the generated relation did not match the goal."
            throwErrorAt ref
              "cega generated a checked {mode.certificateName} certificate, but it does not prove \
               this exact goal. Check the expression, rational box, and requested bounds.\n\
               {detail}\nCertificate projection:{indentD error.toMessageData}\
               {← arithmeticNote explicitExactCall}"
    return result

/-- The bound that a certificate goal states with closed numerals, for the query mode `mode`: the
endpoints of `EnclosedOn f s lo hi` for the enclosure mode, `c` in `BoundOn f s c` for the
upper-bound and absolute-bound modes, and the constant reference `c` and error `ε` of
`ApproxOn f (fun _ ↦ c) s ε` for the midpoint approximation. Only reads the goal; the transport
proves the stated terms equal to these values. -/
private def statedCertificateBound? (mode : BoxQueryMode) (target : Lean.Expr) :
    MetaM (Option StatedBound) := do
  let target := target.consumeMData
  let head := target.getAppFn.consumeMData
  let arguments := target.getAppArgs
  let rational (term : Lean.Expr) : MetaM (Option ℚ) :=
    if term.hasFVar ∨ term.hasMVar then pure none
    else Tactic.BoxInequality.statedRational? term
  match mode with
  | .enclose =>
      unless head.isConstOf ``Certificate.EnclosedOn ∧ arguments.size = 5 do return none
      let some lo ← rational arguments[3]! | return none
      let some hi ← rational arguments[4]! | return none
      return some (.enclosure lo hi)
  | .bound | .absBound =>
      unless head.isConstOf ``Certificate.BoundOn ∧ arguments.size = 4 do return none
      let some c ← rational arguments[3]! | return none
      return some (if mode = .bound then .upper c false else .absolute c false)
  | .approx =>
      unless head.isConstOf ``Certificate.ApproxOn ∧ arguments.size = 7 do return none
      unless arguments[1]!.consumeMData.headBeta.isConstOf ``Real do return none
      let .lam _ _ body _ := arguments[4]!.consumeMData | return none
      if body.hasLooseBVars then return none
      let some center ← rational body | return none
      let some radius ← rational arguments[6]! | return none
      return some (.approx center radius)

/--
The stated-bound route of an explicit query, tried before `closeBoxQuery`: when the goal states
its bound with closed numerals, as `EnclosedOn f s (-1) 1` or `f x ≤ 1 / 4` does, the bound is
checked for the query of `mode` whose enclosure is computed by `method` in one kernel check
(`checkStatedBounds`) and the checked theorem is
transported to the goal as `closeBoxQuery` transports a query result. Returns `false`, with the
state restored, when the route does not apply, when the search route has this query memoized,
when the kernel rejects the check, or when the transport fails; `closeBoxQuery` then runs the
search, whose diagnostics and refusals are the tactic's.
-/
private def closeStatedBoxQuery (mode : BoxQueryMode) (method : EnclosureMethod)
    (precision : Continuum.RationalInterval.Precision) (bindingSyntax : Array Syntax)
    (expression : Syntax) : TacticM Bool :=
  Tactic.ProofCarrier.restoringStateOnFalse <| Tactic.BoxInequality.falseOnFailure do
    let bindings ← parseBindings bindingSyntax
    let reified ← parseExpression expression (bindings.map BoxBinding.coordinate)
    let box := bindings.map BoxBinding.interval
    Tactic.BoxInequality.introduceBinders
    let target ← withMainContext do instantiateMVars (← getMainTarget)
    unless isCertificateTarget target do
      return ← Tactic.BoxInequality.closeWithStatedQuery "cega" method bindings reified.expr
        precision
    let some stated ← statedCertificateBound? mode target | return false
    if ← liftM <| boxQueryMemoized mode method precision box reified.expr then
      return false
    let .checked proofs ← liftM <| checkStatedBounds method precision box reified.expr #[stated]
      | return false
    let some proof := proofs[0]? | return false
    try
      if ← assignValidatedBoxProof? mode proof then
        return true
      trace[cega.stated] "the checked theorem does not transport to the goal; the search runs"
    catch error =>
      trace[cega.stated] "the checked theorem does not transport to the goal; the search runs:\
        {indentD error.toMessageData}"
    return false

/-- The route by which bare `cega` closed a goal. -/
inductive BareRoute where
  /-- A registered checked carrier in the local context or the goal was projected. -/
  | carrier (route : Tactic.CEGA.SelectedRoute)
  /-- A closed decidable statement about floats was decided in the kernel as `float_decide`
  decides it; `replay` is the call `float_decide`. -/
  | floatDecide (replay : TSyntax `tactic)
  /-- An ordinary inequality on bounded real variables, or a conjunction of such inequalities,
  was closed by FloatLib's check or by a checked box query; `query` is the call that runs it
  again, as `Tactic.BoxInequality.closeMainGoal` returns it. -/
  | boxInequality (query : TSyntax `tactic)
  /-- A goal about one interval integral was closed by a checked batch quadrature; `replay` is
  the bare `cega` call that runs it. -/
  | integral (replay : TSyntax `tactic)
  /-- A certificate goal on a coordinate box was unfolded to an ordinary goal and closed by
  FloatLib's check or by a checked box query; `replay` is the bare `cega` call that runs it. -/
  | certificateGoal (replay : TSyntax `tactic)
  /-- A real inequality, a conjunction of real inequalities or a bound over a whole domain was
  proved by FloatLib's `interval`; `replay` is the `interval` call that ran, or bare `cega`
  where the route introduced binders or split a conjunction first. -/
  | interval (replay : TSyntax `tactic)
  /-- A goal without free variables was closed by dyadic interval evaluation with CEGA's
  ranges; `query` is the `dyadic_interval` call that runs it. -/
  | inclusion (query : TSyntax `tactic)

/-- Stable diagnostic label of a bare `cega` route. -/
def BareRoute.label : BareRoute → String
  | .carrier route => route.label
  | .floatDecide _ => "kernel evaluation of a closed statement about floats (float_decide)"
  | .boxInequality _ => "checked box enclosure of an ordinary inequality"
  | .integral _ => "checked batch quadrature of an interval integral"
  | .certificateGoal _ => "checked box enclosure of a certificate goal on a coordinate box"
  | .interval _ => "interval evaluation of a real inequality (FloatLib's interval)"
  | .inclusion _ => "dyadic interval evaluation of a closed goal"

/-- The working bits that a bare call asks for: `n` for `(prec := n)` and about `3.3 d + 8` for
`(digits := d)`; `none` when it sets neither. -/
private def requestedBits? (config : BareConfig) : Option Nat :=
  match config.prec?, config.precision.digits with
  | some bits, _ => some bits
  | none, some digits => some (digits * 3322 / 1000 + 8)
  | none, none => none

/-- The call bare `cega` runs on a closed goal that its other routes refuse. Its working
precision is `n` bits for `(prec := n)`, about `3.3 d + 8` bits for `(digits := d)`, and 32 bits
otherwise. -/
def inclusionQuery (config : BareConfig := {}) : TacticM (TSyntax `tactic) := do
  let bits := (requestedBits? config).getD 32
  `(tactic| dyadic_interval [$(mkIdent `cega_real):ident, $(mkIdent `prec):ident := $(quote bits)])

/--
Close a goal without free variables, such as a conjunction, negation, membership or equality
of real constants, with `dyadic_interval` and the `cega_real` ranges of
`CAS.Continuum.Interval.Inclusion.Elementary`, at the precision of `inclusionQuery`. Goals with
free variables use the box route, which reads their bounds from the hypotheses.
-/
def closeClosedByInclusion (config : BareConfig := {}) : TacticM (TSyntax `tactic) := do
  let target ← withMainContext do instantiateMVars (← getMainTarget)
  if target.hasFVar || target.hasMVar then
    throwError "interval evaluation is tried only on goals without free variables"
  let query ← inclusionQuery config
  evalTactic query
  return query

/-! ## The float_decide route -/

/-- The main goal's statement with its local definitions expanded, when no free variable or
metavariable is left in it. -/
private def closedStatement? : TacticM (Option Expr) := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let target ← if target.hasFVar then zetaReduce target else pure target
  return if target.hasFVar || target.hasMVar then none else some target

/-- Whether `statement` is a proposition with a `Decidable` instance. -/
private def isDecidableProp (statement : Expr) : MetaM Bool := do
  try
    unless ← isProp statement do
      return false
    return (← synthInstance? (mkApp (mkConst ``Decidable) statement)).isSome
  catch _ =>
    return false

/-- The statement that the float_decide route decides: the main goal's statement with its local
definitions expanded, when it is closed, is about the values of a float format
(`FloatLib.Tactic.KernelCheck.mentionsStoredValue`) and has a `Decidable` instance. The test
reads the statement and the signatures of its constants and does no kernel work. It fails on a
statement about natural numbers, integers and rationals alone, such as a certificate on packed
rows. -/
private def floatDecideStatement? : TacticM (Option Expr) := withMainContext do
  let some statement ← closedStatement? | return none
  unless ← FloatLib.Tactic.KernelCheck.mentionsStoredValue statement do
    return none
  return if ← isDecidableProp statement then some statement else none

/-- The refusal of the float_decide route when the proof of `statement` failed with `error`: the
kernel's recursion limit, with a setting that parses; a decision that the kernel did not evaluate
to `true`, with the statement; or else `error` itself, a refusal of `KernelCheck.prove`. -/
private def floatDecideRejection (statement : Expr) (error : Exception) : MetaM MessageData := do
  if ← Tactic.ProofCarrier.isKernelDeepRecursion error then
    let depth := maxRecDepth.get (← getOptions)
    return m!"cega float_decide route: the kernel reached its recursion limit (maxRecDepth \
      {depth}) while evaluating{indentExpr statement}\nThis is a resource limit, not a \
      refutation. To raise the limit, write `set_option maxRecDepth {4 * depth} in` before the \
      tactic."
  unless (← error.toMessageData.toString).startsWith "(kernel)" do
    return m!"cega float_decide route: {error.toMessageData}"
  return m!"cega float_decide route: the kernel did not evaluate{indentExpr statement}\nto \
    `true` after FloatLib's kernel rules rewrote its float operations. The statement may be \
    false; `float_decide` on its own says whether it is."

/-- Prove the main goal, whose statement with its local definitions expanded is `statement`, as
`float_decide` proves it (`FloatLib.Tactic.KernelCheck.prove`), with the heartbeats that the
declaration has left for the kernel (`Tactic.ProofCarrier.runKernelCheck`): a kernel timeout ends
the tactic, and any other failure refuses the route (`floatDecideRejection`). The proof may use
no axiom beyond the three standard ones that the goal does not already use
(`Tactic.ProofCarrier.withKernelOnlyAxioms`), in every checking profile. Returns the call
`float_decide`. -/
private def closeByFloatDecide (statement : Expr) : TacticM (TSyntax `tactic) :=
  Tactic.ProofCarrier.withKernelOnlyAxioms "cega float_decide route" do
    let proof ← Tactic.ProofCarrier.runKernelCheck "cega float_decide route"
      (do
        -- Inside the check, the option holds the heartbeats that the declaration has left.
        let budget := maxHeartbeats.get (← getOptions)
        FloatLib.Tactic.KernelCheck.prove statement (maxHeartbeats := some budget)
          (tactic := `float_decide))
      fun error ↦ do throwError (← floatDecideRejection statement error)
    unless ← Tactic.ProofCarrier.assignExactProof "cega float_decide route" proof do
      throwError "cega float_decide route: the decided statement is not the goal"
    return (← `(tactic| float_decide), #[])

/-! ## The interval route -/

/-- Whether `type` is `ℝ` or `ℝ≥0`. -/
private def isRealType (type : Expr) : Bool :=
  type.consumeMData.isConstOf ``Real || type.consumeMData.isConstOf ``NNReal

/-- Whether `e` is `a ≤ b`, `a < b`, `a ≥ b` or `a > b` between real or nonnegative real
numbers, a relation that FloatLib's `interval` proves. Only the head and the type are read, so
`e` may have loose bound variables. -/
private def isIntervalRelation (e : Expr) : Bool :=
  let e := e.consumeMData
  (e.isAppOfArity ``LE.le 4 || e.isAppOfArity ``LT.lt 4 || e.isAppOfArity ``GE.ge 4 ||
    e.isAppOfArity ``GT.gt 4) && isRealType (e.getArg! 0)

/-- Whether `e` is a relation of `isIntervalRelation` or a conjunction of such relations. -/
private partial def isIntervalConjunction (e : Expr) : Bool :=
  match e.consumeMData.and? with
  | some (left, right) => isIntervalConjunction left && isIntervalConjunction right
  | none => isIntervalRelation e

/-- Whether `target` is a bound over a whole domain in a form that FloatLib's `interval` reads
before any binder is introduced: `∀ u : ℝ, R u`, `∀ x ∈ Set.Icc lo hi, R x` or
`∀ z : ℂ, ‖z‖ = 1 → R z`, with `R` a relation of `isIntervalRelation`. -/
private def isWholeDomainBound (target : Expr) : Bool :=
  match target.consumeMData with
  | .forallE _ domain body _ =>
      let domain := domain.consumeMData
      let premiseAndRelation (premise : Expr → Bool) : Bool :=
        match body.consumeMData with
        | .forallE _ hypothesis conclusion _ =>
            premise hypothesis.consumeMData && isIntervalRelation conclusion
        | _ => false
      if domain.isConstOf ``Real then
        isIntervalRelation body || premiseAndRelation fun hypothesis ↦
          hypothesis.isAppOfArity ``Membership.mem 5 &&
            (hypothesis.getArg! 3).consumeMData.isAppOfArity ``Set.Icc 4
      else if domain.isConstOf ``Complex then
        premiseAndRelation fun hypothesis ↦
          hypothesis.isAppOfArity ``Eq 3 &&
            (hypothesis.getArg! 1).consumeMData.isAppOfArity ``Norm.norm 3
      else
        false
  | _ => false

/-- `target` after its leading universal quantifiers and hypotheses, as
`Tactic.BoxInequality.introduceBinders` introduces them, with the bound variables left loose. -/
private def afterBinders (target : Expr) : Nat → Expr
  | fuel + 1 =>
      match target.consumeMData with
      | .forallE _ _ body _ => afterBinders body fuel
      | other => other
  | 0 => target

/-- How the interval route reads a goal. -/
private inductive IntervalShape where
  /-- A bound over a whole domain (`isWholeDomainBound`), which FloatLib's `interval` reads as
  it is: by its coefficient bounds first and, under `Set.Icc`, by its boxes. -/
  | wholeDomain
  /-- A relation or a conjunction of relations, once the leading binders are introduced. -/
  | relations

/-- The shape of `target` for the interval route, or `none` when the route does not apply: a bound
over a whole domain, or a goal that is a conjunction of relations of `isIntervalRelation` after
its leading binders. The test reads syntax only. -/
private def intervalShape? (target : Expr) : Option IntervalShape :=
  if isWholeDomainBound target then some .wholeDomain
  else if isIntervalConjunction (afterBinders target 64) then some .relations
  else none

/-- Whether `e` mentions a finite sum, a norm, a dot product or a product of a matrix and a
vector, which FloatLib's `interval` expands and the box route reads as a single variable. -/
private def mentionsAggregate (e : Expr) : Bool :=
  (e.find? fun sub ↦ sub.isAppOf ``Finset.sum || sub.isAppOf ``Norm.norm ||
    sub.isAppOf ``dotProduct || sub.isAppOf ``Matrix.mulVec || sub.isAppOf ``Matrix.vecMul).isSome

/-- The goals of the conjunctions of `goal`, split by `And.intro`, in order. -/
private partial def conjuncts (goal : MVarId) : MetaM (List MVarId) := do
  unless (← instantiateMVars (← goal.getType)).consumeMData.isAppOfArity ``And 2 do
    return [goal]
  (← goal.apply (mkConst ``And.intro)).flatMapM conjuncts

/-- The call of FloatLib's `interval` that the interval route runs: `(precision := n)` with the
bits of `requestedBits?` and `(depth := n)` with `depth?`, each only when the call of `cega` sets
it, so that FloatLib's own defaults apply otherwise. -/
private def intervalCall (config : BareConfig) (depth? : Option Nat) :
    TacticM (TSyntax `tactic) := do
  let items := (requestedBits? config).toArray.map (`precision, ·) ++
    depth?.toArray.map (`depth, ·)
  let options := items.map fun (name, _) ↦ mkIdent name
  let values : Array Term := items.map fun (_, value) ↦ quote value
  `(tactic| interval $[($options:ident := $values:term)]*)

/-- Prove the main goal with the `interval` call of `intervalCall`, read as `shape` says: a bound
over a whole domain as it is, and otherwise each relation of the conjunction that the goal is
once its leading binders are introduced (`Tactic.BoxInequality.introduceBinders`). Every kernel
check of `interval` has FloatLib's budget, and the kernel work is charged to the declaration
before and after the route (`Tactic.ProofCarrier.chargeKernelEvaluation`). Returns the call that
replays the route: the `interval` call when it ran once on the goal as stated, and otherwise bare
`cega` with the policy of the call. -/
private def closeByInterval (config : BareConfig) (depth? : Option Nat) (shape : IntervalShape) :
    TacticM (TSyntax `tactic) := do
  Tactic.ProofCarrier.chargeKernelEvaluation "cega interval route"
  let call ← intervalCall config depth?
  let stated ← withMainContext do instantiateMVars (← getMainTarget)
  let replay ← match shape with
    | .wholeDomain =>
        evalTactic call
        pure call
    | .relations =>
        Tactic.BoxInequality.introduceBinders
        let others := (← getGoals).drop 1
        let leaves ← conjuncts (← getMainGoal)
        for leaf in leaves do
          setGoals [leaf]
          try
            evalTactic call
          catch error =>
            if leaves.length == 1 then
              throw error
            throwError "cega interval route: the conjunct\
              {indentExpr (← instantiateMVars (← leaf.getType))}\nwas not proved:\
              {indentD error.toMessageData}"
        setGoals others
        if leaves.length == 1 && !stated.consumeMData.isForall then pure call
        else Tactic.BoxInequality.bareSyntax config.precision
  Tactic.ProofCarrier.chargeKernelEvaluation "cega interval route"
  return replay

/-- The depth of the item `(depth := n)` of a bare call `cega …` whose arguments `arguments`
have the kind `cegaConfigured` or `cegaFloats`, which the interval route gives FloatLib's
`interval`; `none` when the call has no such item, and `interval` then takes its own default. -/
def bareDepth? (arguments : Syntax) : Option Nat :=
  let items := if arguments.isOfKind ``cegaFloats then arguments[5] else arguments[0]
  (CAS.Command.configItems 16 items).findSome? fun item ↦ do
    let (name, value) ← CAS.Command.valueConfigItem? item
    if name == `depth then value.isNatLit? else none

/-- Whether this call is native `cega [fast]`, whose routes may use native certificates. -/
private def nativeFastMode : TacticM Bool := do
  let options ← getOptions
  return options.getBool `cega.nativePolynomial false &&
    options.getBool `cega.nativeCertificates false

/-- Run one route of `cega` as a kernel-only route
(`Tactic.ProofCarrier.withKernelOnlyAxioms`), except inside native `cega [fast]`. A rejected
proof is an ordinary route failure, so the next route is tried. -/
private def kernelOnlyRoute {α : Type} (description : String) (route : TacticM α) :
    TacticM α := do
  if ← nativeFastMode then
    route
  else
    Tactic.ProofCarrier.withKernelOnlyAxioms description do
      return (← route, #[])

/-- The routes of `closeBare`, in the arithmetic that the caller set (`activeArithmetic`), with
the depth `depth?` of the call's item `(depth := n)` for the interval route. The float_decide
route runs only when `floatDecide` holds; native `cega [fast]` runs it before this. -/
private def closeBareRoutes (config : BareConfig) (depth? : Option Nat) (floatDecide : Bool)
    (routeReport? : Option (IO.Ref MessageData)) : TacticM BareRoute := do
  let arithmetic ← activeArithmetic
  -- The box queries subdivide a box whose first query falls short, except in native
  -- `cega [fast]`, whose polynomial certificate does not subdivide.
  let subdivide := !(← nativeFastMode)
  let carrierError ← match ← Tactic.ProofCarrier.attemptClosingMainGoal "cega carrier route"
      (kernelOnlyRoute "cega carrier route" Tactic.CEGA.closeFromLocalCarriers) with
    | .ok closed => return .carrier closed.value
    | .error error => pure error
  let target ← withMainContext do instantiateMVars (← getMainTarget)
  -- A closed statement about floats is decided as `float_decide` decides it, in every arithmetic.
  let mut floatError? : Option Exception := none
  if floatDecide then
    if let some statement ← floatDecideStatement? then
      match ← Tactic.ProofCarrier.attemptClosingMainGoal "cega float_decide route"
          (closeByFloatDecide statement) with
      | .ok closed => return .floatDecide closed.value
      | .error error => floatError? := some error
  let mut integralError? : Option Exception := none
  if (Integration.findIntegral? target).isSome then
    if let .float name .. := arithmetic then
      -- The quadrature computes with exact rationals: it is not run in a float arithmetic.
      integralError? := some <| .error (← getRef) m!"cega integral route: the quadrature of an \
        interval integral computes with exact rationals, so it is not run in {name} \
        arithmetic. `cega [use_floats := false]` runs it."
    else
      -- The quadrature certificate is evaluated in the kernel, also in native `cega [fast]`.
      match ← Tactic.ProofCarrier.attemptClosingMainGoal "cega integral route"
          (kernelOnlyRoute "cega integral route" <|
            withOptions (fun options ↦ options.setBool `cega.nativePolynomial false)
              (Integration.close config)) with
      | .ok closed => return .integral closed.value
      | .error error => integralError? := some error
  let preparation ← IO.mkRef Tactic.BoxInequality.CertificatePreparation.notCertificate
  let certificateError ← match ← Tactic.ProofCarrier.attemptClosingMainGoal
      "cega certificate route" (kernelOnlyRoute "cega certificate route" do
        preparation.set (← Tactic.BoxInequality.prepareCertificateGoal)
        let .prepared ← preparation.get
          | throwError "this goal is not a certificate proposition on a coordinate box"
        discard <| Tactic.BoxInequality.closeMainGoal "cega" config.precision subdivide
        Tactic.BoxInequality.bareSyntax config.precision) with
    | .ok closed => return .certificateGoal closed.value
    | .error error => pure error
  let preparation ← preparation.get
  let certificate := match preparation with
    | .notCertificate => false
    | _ => true
  -- A certificate goal is the certificate route's goal; the box route reads ordinary goals.
  let mut boxError? : Option Exception := none
  unless certificate do
    match ← Tactic.ProofCarrier.attemptClosingMainGoal "cega box route"
        (kernelOnlyRoute "cega box route"
          (Tactic.BoxInequality.closeMainGoal "cega" config.precision subdivide)) with
    | .ok closed => return .boxInequality closed.value
    | .error error => boxError? := some error
  let mut intervalError? : Option Exception := none
  if let some shape := intervalShape? target then
    if let .float name .. := arithmetic then
      -- `interval` computes with exact rationals and rational grid points.
      intervalError? := some <| .error (← getRef) m!"cega interval route: FloatLib's `interval` \
        computes with exact rationals, so it is not run in {name} arithmetic. \
        `cega [use_floats := false]` runs it."
    else
      match ← Tactic.ProofCarrier.attemptClosingMainGoal "cega interval route"
          (kernelOnlyRoute "cega interval route" (closeByInterval config depth? shape)) with
      | .ok closed => return .interval closed.value
      | .error error => intervalError? := some error
  let mut inclusionError? : Option Exception := none
  if !target.hasFVar && !target.hasMVar then
    if let .float name .. := arithmetic then
      -- `dyadic_interval` computes with exact dyadic rationals.
      inclusionError? := some <| .error (← getRef) m!"`dyadic_interval` computes with exact \
        dyadic rationals, so it is not run in {name} arithmetic. \
        `cega [use_floats := false]` runs it."
    else
      match ← Tactic.ProofCarrier.attemptClosingMainGoal "cega dyadic_interval route"
          (kernelOnlyRoute "cega dyadic_interval route" (closeClosedByInclusion config)) with
      | .ok closed => return .inclusion closed.value
      | .error error => inclusionError? := some error
  -- The first route whose shape fits the goal leads the refusal, and the other routes follow.
  let head ← Tactic.BoxInequality.describeHead target
  let recognized := (← withMainContext do Tactic.BoxInequality.recognize? target).isSome
  let mut lead? : Option MessageData := floatError?.map (·.toMessageData)
  if lead?.isNone then
    lead? := integralError?.map (·.toMessageData)
  if lead?.isNone then
    match preparation with
    | .notBox domain coordinate =>
        lead? := some (← withMainContext <| addMessageContext m!"This goal has {head}, a \
          certificate proposition whose domain{indentExpr domain}\nis not a coordinate box: it \
          gives no rational bounds on {coordinate}. `cega using h` projects a checked carrier \
          `h`, and `cega [enclose x in [a, b]] expr` synthesizes one on a rational box.")
    | .prepared => lead? := some certificateError.toMessageData
    | .notCertificate => pure ()
  let mut others := #[m!"carrier search:{indentD carrierError.toMessageData}"]
  -- The box route leads on an inequality it reads, unless the interval route applied to an
  -- aggregate, which only `interval` expands.
  let boxLeads := recognized && !(intervalError?.isSome && mentionsAggregate target)
  if let some boxError := boxError? then
    if lead?.isNone && boxLeads then
      lead? := some boxError.toMessageData
    else
      others := others.push m!"box route:{indentD boxError.toMessageData}"
  if let some intervalError := intervalError? then
    if lead?.isNone then
      lead? := some intervalError.toMessageData
    else
      others := others.push m!"interval route:{indentD intervalError.toMessageData}"
  if let some inclusionError := inclusionError? then
    others := others.push m!"dyadic_interval route:{indentD inclusionError.toMessageData}"
  let lead := lead?.getD
    m!"This goal has {head}; its outer shape is not supported by these routes."
  let body := m!"{lead}\nOther routes:{indentD (MessageData.joinSep others.toList m!"\n")}"
  if let some report := routeReport? then
    report.set body
  throwError "{body}\n\
    Bare `cega` proves an ordinary real inequality ({Tactic.BoxInequality.supportedShapes}), a \
    bound on an interval integral `∫ x in a..b, f x` with rational limits, a certificate goal \
    (`EnclosedOn f s lo hi`, `BoundOn f s c`, `ApproxOn f g s ε`, `ResidualBound r s ε`) on a \
    coordinate box or from a checked carrier in the local context or the goal, a closed \
    decidable statement about floats, which `float_decide` decides, a real inequality that \
    FloatLib's `interval` proves, on finite sums and norms too, and a closed goal that interval \
    evaluation proves."

/-- The arithmetic of a bare call: the one that its configuration resolved from the flag
`use_floats` and the item `(arith := F)`, or else that of the option `cega.arithmetic`. -/
def resolveArithmetic (config : BareConfig) : TacticM Arithmetic :=
  match config.arithmetic? with
  | some arithmetic => pure arithmetic
  | none => ({} : ArithmeticRequest).resolve

/-- `config` with its arithmetic resolved to `arithmetic`. In a float arithmetic only the depth
of the precision policy is kept: the other fields configure the series of the exact evaluator,
which a float query does not run, so messages and replays do not show them. -/
private def withResolvedArithmetic (arithmetic : Arithmetic) (config : BareConfig) : BareConfig :=
  if arithmetic.isFloat then
    { config with
      precision := { depth := config.precision.depth }
      prec? := none
      arithmetic? := some arithmetic }
  else
    { config with arithmetic? := some arithmetic }

/--
Close the goal by the routes of bare `cega`, in this order: a matching checked carrier from the
local context or the goal; for a closed decidable statement about floats, the kernel decision of
`float_decide` (`closeByFloatDecide`); for a goal about one interval integral, the checked batch
quadrature of `Integration.close`; for a certificate goal whose domain is a coordinate box,
FloatLib's check or else the checked box query on the coordinates of its point
(`Tactic.BoxInequality.prepareCertificateGoal`); for an ordinary inequality on real variables
bounded by rational literal hypotheses, the same on the box those hypotheses describe
(`Tactic.BoxInequality.closeMainGoal`); for a real inequality, a conjunction of them or a bound over
a whole domain, FloatLib's `interval` (`closeByInterval`), with the precision of `(prec := n)` or
`(digits := d)` and the depth `depth?` of the call's item `(depth := n)`; and for a goal without
free variables, the interval evaluation of `inclusionQuery`. Each route reads the shape of the
goal first and runs only when it fits. A refusal leads with the reason of the first route whose
shape fits (`float_decide`, the integral route, the certificate route, the box route for a
recognized inequality without a finite sum, norm or matrix product that the interval route
applied to, or the interval route), or else names the goal's head, and then gives the
other routes' reasons and the supported shapes. Each route is kernel-only (`kernelOnlyRoute`)
unless this is native `cega [fast]`, and `float_decide` is kernel-only there too. A refusal also
stores its reasons in `routeReport?`, when it is given, so that a caller can report them under
its own headline. With `floatDecide := false` the float_decide route is not run, as after native
`cega [fast]` has run it.

The routes run in the arithmetic of the call (`resolveArithmetic`, `withArithmetic`). In a float
format the box queries of the certificate route and of the box route compute with float
intervals, the carrier route and `float_decide` run as they are, and the integral route,
`interval` and the interval evaluation, which compute with exact numbers, are not run: each
refuses with that reason.
-/
def closeBare (config : BareConfig := {})
    (routeReport? : Option (IO.Ref MessageData) := none) (depth? : Option Nat := none)
    (floatDecide : Bool := true) : TacticM BareRoute := do
  let arithmetic ← resolveArithmetic config
  withArithmetic arithmetic
    (closeBareRoutes (withResolvedArithmetic arithmetic config) depth? floatDecide routeReport?)

/-- Close a fully specified finite certificate without using local assumptions. -/
private def closeFiniteCertificate (native : Bool) : TacticM Unit := withMainContext do
  let proof ← decideClosedCertificate (← getMainTarget) native
  let assigned ← profileitM Exception "CEGA finite proof validation" (← getOptions) do
    Tactic.ProofCarrier.assignExactProof "CEGA finite certificate" proof
  unless assigned do
    throwError "CEGA finite certificate did not match the goal"

/-- Whether the main goal, with its local definitions expanded, is a closed proposition with a
`Decidable` instance: the goal of the finite certificate, which expands them the same way. -/
private def closedDecidableTarget : TacticM Bool := do
  let some statement ← closedStatement? | return false
  isDecidableProp statement

/-- Keep the semantic routes first, then, for a closed decidable proposition, try a kernel
certificate. When that certificate applies to the goal and the kernel fails on it, its failure
leads the report. The certificate is not tried on a statement about floats
(`floatDecideStatement?`): the float_decide route has decided that statement with the kernel
rules, and the certificate would decide it again without them. In a float arithmetic the
certificate is not tried on a goal that the box route reads (`Tactic.BoxInequality.recognize?`),
so that a float query that falls short is never followed by another computation. `depth?` and
`floatDecide` are those of `closeBare`. -/
private def closeKernelOrBare (config : BareConfig := {}) (depth? : Option Nat := none)
    (floatDecide : Bool := true) : TacticM Unit := do
  let arithmetic ← resolveArithmetic config
  let config := { config with arithmetic? := some arithmetic }
  let routeReport ← IO.mkRef m!""
  match ← Tactic.ProofCarrier.attemptClosingMainGoal "CEGA semantic routes"
      (discard <| closeBare config (some routeReport) depth? floatDecide) with
  | .ok _ => pure ()
  | .error semanticError =>
      unless ← closedDecidableTarget do
        throw semanticError
      -- A statement about floats is the float_decide route's, and its refusal is the answer.
      if (← floatDecideStatement?).isSome then
        throw semanticError
      -- In a float arithmetic, a goal that the box route reads is the float query's goal, and
      -- its refusal is the answer: no decision procedure is tried in its place.
      if arithmetic.isFloat then
        let target ← withMainContext do instantiateMVars (← getMainTarget)
        if (← withMainContext do Tactic.BoxInequality.recognize? target).isSome then
          throw semanticError
      match ← Tactic.ProofCarrier.attemptClosingMainGoal "CEGA finite kernel certificate"
          (kernelOnlyRoute "CEGA finite kernel certificate" (closeFiniteCertificate false)) with
      | .ok _ => pure ()
      | .error finiteError =>
          -- A closed statement with a decision procedure is the finite route's goal: its kernel
          -- failure leads the report, and the other routes follow without their refusal of the
          -- goal's shape.
          if Tactic.KernelReadBack.isKernelCertificateFailure finiteError then
            throwError "{finiteError.toMessageData}\n\
              This is a closed statement with a decision procedure, which `cega` proves by \
              evaluating it in the kernel; its other routes, for certificate goals, interval \
              integrals and real inequalities, did not apply either:\
              {indentD (← routeReport.get)}"
          throwError "{semanticError.toMessageData}\n{finiteError.toMessageData}"

/-- The native profile of `cega [fast]`: for a closed decidable statement about floats the kernel
decision of `float_decide`, then for a closed decidable proposition a finite certificate by
native evaluation, then the other semantic routes with the native polynomial enclosure. In a
float arithmetic the semantic routes run without it: a float enclosure is evaluated in the
kernel. `depth?` is that of `closeBare`. -/
private def closeFast (config : BareConfig := {}) (depth? : Option Nat := none) :
    TacticM Unit := do
  let arithmetic ← resolveArithmetic config
  let config := { config with arithmetic? := some arithmetic }
  let mut failures : Array MessageData := #[]
  if let some statement ← floatDecideStatement? then
    match ← Tactic.ProofCarrier.attemptClosingMainGoal "cega float_decide route"
        (closeByFloatDecide statement) with
    | .ok _ => return
    | .error error => failures := failures.push m!"float_decide: {error.toMessageData}"
  if ← closedDecidableTarget then
    match ← Tactic.ProofCarrier.attemptClosingMainGoal "CEGA finite native certificate"
        (closeFiniteCertificate true) with
    | .ok _ =>
        trace[cega.native] "Finite native proof assigned and validated"
        return
    | .error error =>
        -- The probe has restored its state, so this diagnostic survives its rollback.
        trace[cega.native] "Finite native attempt refused; trying semantic CEGA:\n\
          {error.toMessageData}"
        failures := failures.push m!"Finite native attempt: {error.toMessageData}"
  try
    -- A float enclosure is evaluated in the kernel only.
    withOptions (fun options ↦ options.setBool `cega.nativePolynomial !arithmetic.isFloat)
      (discard <| closeBare config none depth? (floatDecide := false))
  catch semanticError =>
    if semanticError.isRuntime then
      throw semanticError
    if failures.isEmpty then
      throw semanticError
    throwError "{MessageData.joinSep failures.toList m!"\n"}\n\
      Semantic CEGA attempt: {semanticError.toMessageData}"

/-- Bare `cas` dispatches ordinary inequalities on rational boxes to the box route once this
module is imported. -/
@[cas_route box]
def boxRoute : Tactic.RouteRegistry.Closer := fun _ ↦ do
  Tactic.ProofCarrier.withKernelOnlyAxioms "cas box route" do
    return ({ replay := ← Tactic.BoxInequality.closeMainGoal "cas" }, #[])

/-- The routes of `cega [fast]` with the configuration `config` and the depth `depth?` of its
item `(depth := n)`: bare `cega` without native checking, and otherwise the native profile
(`closeFast`), then bare `cega` without the float_decide route, which the native profile ran,
when it fails. -/
private def closeFastOrBare (config : BareConfig := {}) (depth? : Option Nat := none) :
    TacticM Unit := do
  -- Without native checking, `cega [fast]` is bare `cega`, run once.
  unless (← getOptions).getBool `cega.nativeCertificates false do
    return ← closeKernelOrBare config depth?
  let saved ← saveState
  tryCatchRuntimeEx
    (closeFast config depth?)
    fun error ↦ do
      saved.restore
      if error.isRuntime then
        throw error
      trace[cega.native] "Fast CEGA restored state; using kernel fallback:\n\
        {error.toMessageData}"
      try
        closeKernelOrBare config depth? (floatDecide := false)
      catch kernelError =>
        let .error .. := kernelError | throw kernelError
        throwError "{kernelError.toMessageData}\n\
          The native attempt of `cega [fast]`, before this kernel fallback, failed with:\
          {indentD error.toMessageData}"

/--
Close the goal by projecting a matching checked CEGA carrier found in the local context or
target, by `float_decide` on a closed decidable statement about floats, by the checked batch
quadrature of a goal about one interval integral, by FloatLib's check or else the checked box query
of a certificate goal on a coordinate box or of an ordinary inequality on real variables bounded by
rational literal hypotheses, by FloatLib's `interval` on a real inequality, or, for a closed goal
that these routes refuse, by `dyadic_interval [cega_real, prec := n]` at the precision of
`inclusionQuery`. A closed decidable proposition that all of these refuse, and that is not about
floats, is evaluated in the kernel (`closeKernelOrBare`).
-/
elab_rules : tactic
  | `(tactic| cega) =>
      Tactic.ProofCarrier.tacticEntry "cega" closeKernelOrBare
  | `(tactic| cega [fast]) => Tactic.ProofCarrier.tacticEntry "cega [fast]" closeFastOrBare
  | `(tactic| cega using $carrier:term) =>
      Tactic.ProofCarrier.tacticEntry "cega using" <|
        Tactic.ProofCarrier.withKernelOnlyAxioms "cega using" do
          let (_, carrierExpr) ← Tactic.CEGA.closeUsingCarrier carrier
          return ((), #[carrierExpr])

/-- The configuration of a bare call from its configuration items `items` and from the flag
`use_floats := b` of its bracket group, `floats?`. The item `(arith := F)` is taken out of the
items (`splitArithmeticItem`), and the arithmetic is resolved when the call has the flag or the
item (`ArithmeticRequest.resolve`); a call with neither keeps `arithmetic? := none`, which
`closeBare` resolves from the option `cega.arithmetic`. -/
def bareConfig (items : Syntax) (floats? : Option Bool := none) : TacticM BareConfig := do
  let (format?, others) ← splitArithmeticItem items
  let config ← parseBareConfig (if format?.isSome then others else items)
  if format?.isNone ∧ floats?.isNone then
    return config
  let arithmetic ← ({ floats?, format? } : ArithmeticRequest).resolve
  return { config with arithmetic? := some arithmetic }

/-- Bare `cega` with the precision policy, subdivision depth, panel count and arithmetic of its
configuration items. -/
@[tactic tacticCega]
def evalCegaConfigured : Tactic := fun stx ↦ do
  let arguments := stx[1][0]
  unless arguments.isOfKind ``cegaConfigured do throwUnsupportedSyntax
  Tactic.ProofCarrier.tacticEntry "cega" do
    closeKernelOrBare (← bareConfig arguments[0]) (bareDepth? arguments)

/-- The configuration of a call `cega [… use_floats …] items`, whose arguments `arguments` have
the kind `cegaFloats`, when `fast` is its only other flag, with whether it has that flag; `none`
when it has a flag of another module, such as `batch := n`, which that module elaborates. -/
def floatsConfig? (arguments : Syntax) : TacticM (Option (BareConfig × Bool)) := do
  let flags := otherFlags arguments
  unless flags.all (·.isOfKind ``cegaFlagFast) do
    return none
  if h : 1 < flags.size then
    throwErrorAt flags[1] "the flag `fast` is given twice"
  return some (← bareConfig arguments[5] (some (useFloats arguments)), !flags.isEmpty)

/-- `cega [use_floats]` and `cega [fast, use_floats]`, with their configuration items: bare
`cega`, or `cega [fast]`, in the arithmetic that the flag and the item `(arith := F)` ask for
(`bareConfig`). -/
@[tactic tacticCega]
def evalCegaFloats : Tactic := fun stx ↦ do
  let arguments := stx[1][0]
  unless arguments.isOfKind ``cegaFloats do throwUnsupportedSyntax
  let some (config, fast) ← floatsConfig? arguments | throwUnsupportedSyntax
  Tactic.ProofCarrier.tacticEntry "cega" do
    let depth? := bareDepth? arguments
    if fast then closeFastOrBare config depth? else closeKernelOrBare config depth?

/--
`cega using carrier`

Close the goal by projecting one explicitly supplied checked CEGA carrier.
-/
tactic_extension tacticCega

/-- The query mode an explicit query runs for the main goal, the projection the goal needs: an
enclosure for `EnclosedOn`, an upper bound for `BoundOn f s c`, an absolute bound for
`BoundOn (fun x ↦ |f x|) s c`, a midpoint approximation for `ApproxOn`, and the mode of the shape
of an ordinary inequality (`Tactic.BoxInequality.Shape.mode`). The mode does not depend on how
the enclosure is computed: `(depth := n)` subdivides the box for every mode. -/
private def explicitQueryMode : TacticM BoxQueryMode := do
  let target ← withMainContext do instantiateMVars (← getMainTarget)
  let target := target.consumeMData
  let head := target.getAppFn.consumeMData
  if head.isConstOf ``Certificate.BoundOn then
    let absolute : Bool := match target.getAppArgs[1]?.map Lean.Expr.consumeMData with
      | some (.lam _ _ body _) => body.consumeMData.isAppOf ``abs
      | _ => false
    return bif absolute then .absBound else .bound
  if head.isConstOf ``Certificate.ApproxOn then
    return .approx
  if head.isConstOf ``Certificate.EnclosedOn then
    return .enclose
  match ← withMainContext do Tactic.BoxInequality.recognize? target with
  | some recognized => return recognized.shape.mode
  | none => return .enclose

/-- Close the main goal with the explicit query `cega cfg [enclose bindings] expression` as a
kernel-only route (`Tactic.ProofCarrier.withKernelOnlyAxioms`), in the mode the goal needs
(`explicitQueryMode`), with the enclosure method that `cfg` requests (`requestedMethod`) and in
the arithmetic of its item `(arith := F)`, or else of the option `cega.arithmetic`: the
stated-bound route first (`closeStatedBoxQuery`), then the search (`closeBoxQuery`). Returns the
mode, the method and the arithmetic. -/
def closeEncloseQuery (cfg : Syntax) (bindings : Array Syntax) (expression : Syntax) :
    TacticM (BoxQueryMode × EnclosureMethod × Arithmetic) := do
  let (format?, others) ← splitArithmeticItem cfg
  let cfg := if format?.isSome then others else cfg
  let arithmetic ← ({ format? } : ArithmeticRequest).resolve
  withArithmetic arithmetic <| Tactic.ProofCarrier.withKernelOnlyAxioms "cega [enclose]" do
    let precision ← parsePrecision cfg
    -- A float query reads only the depth of the policy.
    let precision : Continuum.RationalInterval.Precision :=
      if arithmetic.isFloat then { depth := precision.depth } else precision
    let method := requestedMethod cfg
    Tactic.BoxInequality.introduceBinders
    let mode ← explicitQueryMode
    unless ← closeStatedBoxQuery mode method precision bindings expression do
      discard <| closeBoxQuery expression mode method precision bindings expression
    return ((mode, method, arithmetic), #[])

elab_rules : tactic
  | `(tactic| cega $cfg:optConfig [enclose $bindings:cegaIntervalBinding,*] $expr:term) =>
      Tactic.ProofCarrier.tacticEntry "cega [enclose]" do
        discard <| closeEncloseQuery cfg bindings.getElems expr

end CAS.CEGA

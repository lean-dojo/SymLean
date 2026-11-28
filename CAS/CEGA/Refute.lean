/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Certificate.Relations
public import CAS.CEGA.Check
public import FloatLib.Numerics.Enclosure.Expression.ConstraintProof

/-!
# Stated bounds on a box, proved by FloatLib's refutation check

A goal such as `x * (1 - x) ≤ 1 / 3` for `x ∈ [0, 1]` holds when its negation has no point in
the box. `Bound` holds the bounds that `cega` reads from a goal, with rational constants: upper,
lower and absolute bounds, strict or not, the approximation of a value by a center, and
conjunctions of these. `Bound.negation` writes the failure of a bound, for the value of a FloatLib
expression, as one FloatLib `Constraint`: `v ≤ c` fails where `v - c` is positive, `|v| ≤ c`
where `|v| - c` is, `|v - m| ≤ r` where `|v - m| - r` is, and a conjunction where one of its
parts fails, so a two-sided bound becomes a disjunction. A refutation of that constraint, which
FloatLib's `Constraint.refutes` accepts on the translation of the expression (`toFloatLib`) and on
the box (`Check.toBox`), proves the bound at every point of the box (`holds_of_refutes`). This
holds for every backend of `Check.Endpoints`, exact or rounded into a floating-point format. The
corollaries `enclosedOn_of_refutes` to `approxOn_of_refutes` state the result as `CAS.CEGA.Query`
states the bounds of a query that pass a Boolean test, so the transports of the box route take a
refutation as they take a query.

`Refute.plan` searches for a refutation in compiled code. It tests each atom of the constraint on
the whole box with FloatLib's check, and bisects a box on which the check fails, at the coordinate
that a function it is given picks, until every part passes or its budget runs out. The half that
is further from passing is searched first, so a bound that fails near a point is given up early.
A disjunction is refuted part by part, each part with its own bisections. Nothing it computes is
trusted: the kernel checks the refutation it returns. `Refute.sensitiveCoordinate` is the pick of
the exact planner, the sensitivity heuristic of the registry, and FloatLib's `Box.widest?` is the
widest coordinate.

## Main definitions

* `Bound`, `Bound.Holds`, `Bound.negation`: stated bounds, what they say of a real value, and
  their failure as a FloatLib constraint.
* `Refute.upperEnd`, `Refute.passes`: the upper end of FloatLib's enclosure of an atom on a box,
  and its test.
* `Refute.descend`, `Refute.planAtom`, `Refute.plan`: the search for a refutation by bisection.
* `Refute.sensitiveCoordinate`: the coordinate that the sensitivity heuristic picks.

## Main results

* `Bound.holds_of_not_negation`: a bound holds wherever its negation does not.
* `holds_of_refutes`: an accepted refutation proves the bound at every point of the box.
* `enclosedOn_of_refutes`, `boundOn_of_refutes`, `lt_of_refutes`, `le_of_refutes_lower`,
  `lt_of_refutes_lower`, `boundOn_abs_of_refutes`, `abs_lt_of_refutes`, `approxOn_of_refutes`:
  each kind of bound, stated as the corresponding `..._of_check` theorem states it.

## Implementation notes

`CAS.Tactic.BoxInequality` has the kernel decide the refutation through FloatLib's
`KernelCheck.prove`, on a statement `Constraint.refutes B r c box = true` whose backend,
refutation, constraint and box are FloatLib's constants and quoted data, so that a kernel rule of
FloatLib on `Constraint.refutes`, `Expr.checkZero` or a backend reaches it. The theorems here
relate that statement to the goal through `Check.Endpoints.backend`, `Bound.negation`,
`toFloatLib` and `Check.toBox`, which the kernel unfolds once, when it checks the theorem that
applies them.

The planner tests a box with the check that the kernel evaluates at a leaf `Refutation.atom 0`,
`Expr.checkZero` without its own bisections (`Refute.upperEnd` and `Refute.passes` take the steps
of `Expr.checkBoxZero`), and it cuts with FloatLib's `Box.halve`, as `Constraint.refutes` does, so
a refutation that the planner finds with the backend of the decision is one that the kernel
accepts. A caller may also plan with another backend, such as a cheaper one that rounds like the
decision; the kernel then decides whether the refutation holds for the backend of the decision.

## References

* Ramon E. Moore, R. Baker Kearfott and Michael J. Cloud, *Introduction to Interval Analysis*,
  SIAM, Philadelphia, 2009, <https://doi.org/10.1137/1.9780898717716>. Chapter 6 for the
  refinement of interval extensions by subdivision.
-/

@[expose] public section

open FloatLib.Numerics hiding RationalInterval
open FloatLib.Numerics.Interval
open CAS.Certificate CAS.Continuum CAS.Continuum.RationalInterval

namespace CAS.CEGA

/-- A bound on a real value with rational constants, as a goal states it: one relation, or the
conjunction of two bounds. -/
inductive Bound where
  /-- `v ≤ c`, or `v < c` when `strict`. -/
  | upper (c : ℚ) (strict : Bool)
  /-- `c ≤ v`, or `c < v` when `strict`. -/
  | lower (c : ℚ) (strict : Bool)
  /-- `|v| ≤ c`, or `|v| < c` when `strict`. -/
  | absolute (c : ℚ) (strict : Bool)
  /-- `|v - center| ≤ radius`. -/
  | approx (center radius : ℚ)
  /-- Both bounds. -/
  | and (left right : Bound)
  deriving Repr, Inhabited

namespace Bound

/-- What the bound says of the real value `v`. -/
def Holds : Bound → ℝ → Prop
  | .upper c false, v => v ≤ c
  | .upper c true, v => v < c
  | .lower c false, v => c ≤ v
  | .lower c true, v => c < v
  | .absolute c false, v => |v| ≤ c
  | .absolute c true, v => |v| < c
  | .approx center radius, v => |v - center| ≤ radius
  | .and a b, v => a.Holds v ∧ b.Holds v

/-- The relation of the value minus the bound where the bound holds: `≤ 0` for a non-strict bound
and `< 0` for a strict one. The bound fails where this relation fails (`negation`). -/
def relation : Bool → Relation
  | false => .nonpositive
  | true => .negative

/--
The FloatLib constraint that holds at a point where the bound fails for the value of `e`:
`fails (relation strict) (e - c)` for an upper bound `c`, `fails (relation strict) (c - e)` for a
lower one, `fails (relation strict) (|e| - c)` for an absolute one,
`fails .nonpositive (|e - center| - radius)` for an approximation, and the disjunction of the
negations of the two parts of a conjunction (`holds_of_not_negation`).
-/
def negation (e : Interval.Expr) : Bound → Constraint
  | .upper c strict => .fails (relation strict) (.binary .sub e (.const c))
  | .lower c strict => .fails (relation strict) (.binary .sub (.const c) e)
  | .absolute c strict => .fails (relation strict) (.binary .sub (.unary .abs e) (.const c))
  | .approx center radius =>
      .fails .nonpositive
        (.binary .sub (.unary .abs (.binary .sub e (.const center))) (.const radius))
  | .and a b => .or (a.negation e) (b.negation e)

/-- A bound holds of the value of `e`, at the inputs `values` and with the call table
`functions`, wherever its negation does not hold. -/
theorem holds_of_not_negation {e : Interval.Expr} {values : ℕ → ℝ}
    {functions : ℕ → List ℝ → ℝ} :
    ∀ bound : Bound, ¬ (bound.negation e).Holds values functions →
      bound.Holds (e.eval values functions)
  | .upper c false, h | .upper c true, h | .lower c false, h | .lower c true, h
  | .absolute c false, h | .absolute c true, h | .approx c _, h => by
    simpa [negation, relation, Holds, Constraint.Holds, Relation.Holds, Interval.Expr.eval,
      UnaryOp.eval, BinaryOp.eval] using h
  | .and a b, h => by
    simp only [negation, Constraint.Holds, not_or] at h
    exact ⟨holds_of_not_negation a h.1, holds_of_not_negation b h.2⟩

end Bound

/--
**FloatLib's refutation check proves a stated bound on a box.** If FloatLib's `Constraint.refutes`
accepts a refutation `r` of the negation of `bound` for the translation of `expr`
(`Bound.negation`, `toFloatLib Fin.val`) on the box `Check.toBox box`, with the backend of
`endpoints` and its standard calls at the settings `config`, then `bound` holds of the value of
`expr` at every point of the CEGA box `box`. This is `Constraint.refutes_sound` at the point
(`Check.containsReal_toBox`), with `Bound.holds_of_not_negation` and `eval_toFloatLib`.
-/
theorem holds_of_refutes (endpoints : Check.Endpoints) (config : Backend.Config) {n : ℕ}
    {box : Fin n → RationalInterval} {expr : Verified.Expr (Fin n)} {bound : Bound}
    {r : Refutation}
    (h : (bound.negation (expr.toFloatLib Fin.val)).refutes (endpoints.backend config) r
      (Check.toBox box) = true) :
    ∀ x ∈ boxDomain box, bound.Holds (expr.eval fun i ↦ x i) := by
  intro x hx
  have hrefuted := Constraint.refutes_sound (endpoints.backend_sound config) r h
    (Check.containsReal_toBox hx)
  rw [← expr.eval_toFloatLib Fin.val (fun i ↦ x i) _ (Check.toValues_val _)]
  exact bound.holds_of_not_negation hrefuted

variable (endpoints : Check.Endpoints) (config : Backend.Config) {n : ℕ}
  {box : Fin n → RationalInterval} {expr : Verified.Expr (Fin n)} {r : Refutation}

/-- A refutation of the failure of `lo ≤ expr ∧ expr ≤ hi` proves
`EnclosedOn expr (boxDomain box) lo hi`, as `enclosedOn_of_check` does for a query. -/
theorem enclosedOn_of_refutes (lo hi : ℚ)
    (h : (((Bound.lower lo false).and (.upper hi false)).negation
      (expr.toFloatLib Fin.val)).refutes (endpoints.backend config) r (Check.toBox box) = true) :
    EnclosedOn (fun x ↦ expr.eval fun i ↦ x i) (boxDomain box) (lo : ℝ) (hi : ℝ) :=
  holds_of_refutes (bound := (Bound.lower lo false).and (.upper hi false)) endpoints config h

/-- A refutation of the failure of `expr ≤ c` proves `BoundOn expr (boxDomain box) c`, as
`boundOn_of_check` does for a query. -/
theorem boundOn_of_refutes (c : ℚ)
    (h : ((Bound.upper c false).negation (expr.toFloatLib Fin.val)).refutes
      (endpoints.backend config) r (Check.toBox box) = true) :
    BoundOn (fun x ↦ expr.eval fun i ↦ x i) (boxDomain box) (c : ℝ) :=
  holds_of_refutes (bound := .upper c false) endpoints config h

/-- A refutation of the failure of `expr < c` proves `expr < c` at every point of the box, as
`lt_of_check` does for a query. -/
theorem lt_of_refutes (c : ℚ)
    (h : ((Bound.upper c true).negation (expr.toFloatLib Fin.val)).refutes
      (endpoints.backend config) r (Check.toBox box) = true) :
    ∀ x ∈ boxDomain box, expr.eval (fun i ↦ x i) < (c : ℝ) :=
  holds_of_refutes (bound := .upper c true) endpoints config h

/-- A refutation of the failure of `c ≤ expr` proves `c ≤ expr` at every point of the box, as
`le_of_check_lower` does for a query. -/
theorem le_of_refutes_lower (c : ℚ)
    (h : ((Bound.lower c false).negation (expr.toFloatLib Fin.val)).refutes
      (endpoints.backend config) r (Check.toBox box) = true) :
    ∀ x ∈ boxDomain box, (c : ℝ) ≤ expr.eval fun i ↦ x i :=
  holds_of_refutes (bound := .lower c false) endpoints config h

/-- A refutation of the failure of `c < expr` proves `c < expr` at every point of the box, as
`lt_of_check_lower` does for a query. -/
theorem lt_of_refutes_lower (c : ℚ)
    (h : ((Bound.lower c true).negation (expr.toFloatLib Fin.val)).refutes
      (endpoints.backend config) r (Check.toBox box) = true) :
    ∀ x ∈ boxDomain box, (c : ℝ) < expr.eval fun i ↦ x i :=
  holds_of_refutes (bound := .lower c true) endpoints config h

/-- A refutation of the failure of `|expr| ≤ c` proves `BoundOn |expr| (boxDomain box) c`, as
`boundOn_abs_of_check` does for a query. -/
theorem boundOn_abs_of_refutes (c : ℚ)
    (h : ((Bound.absolute c false).negation (expr.toFloatLib Fin.val)).refutes
      (endpoints.backend config) r (Check.toBox box) = true) :
    BoundOn (fun x ↦ |expr.eval fun i ↦ x i|) (boxDomain box) (c : ℝ) :=
  holds_of_refutes (bound := .absolute c false) endpoints config h

/-- A refutation of the failure of `|expr| < c` proves `|expr| < c` at every point of the box, as
`abs_lt_of_check` does for a query. -/
theorem abs_lt_of_refutes (c : ℚ)
    (h : ((Bound.absolute c true).negation (expr.toFloatLib Fin.val)).refutes
      (endpoints.backend config) r (Check.toBox box) = true) :
    ∀ x ∈ boxDomain box, |expr.eval fun i ↦ x i| < (c : ℝ) :=
  holds_of_refutes (bound := .absolute c true) endpoints config h

/-- A refutation of the failure of `|expr - center| ≤ radius` proves
`ApproxOn expr (fun _ ↦ center) (boxDomain box) radius`, as `approxOn_of_check` does for a
query. -/
theorem approxOn_of_refutes (center radius : ℚ)
    (h : ((Bound.approx center radius).negation (expr.toFloatLib Fin.val)).refutes
      (endpoints.backend config) r (Check.toBox box) = true) :
    ApproxOn (fun x ↦ expr.eval fun i ↦ x i) (fun _ ↦ (center : ℝ)) (boxDomain box)
      (radius : ℝ) := fun x hx ↦ by
  simpa only [Real.norm_eq_abs, Bound.Holds] using
    holds_of_refutes (bound := .approx center radius) endpoints config h x hx

/-! ## The search for a refutation -/

namespace Refute

variable {α : Type*}

/-- The upper end of FloatLib's enclosure of `e` on `box` by the backend `B`, as
`Expr.checkBoxZero` reads it: the box rounded outward into the ends of `B` (`Box.enclose?`), `e`
evaluated on it with the zero rule (`Expr.evalZero?`), and the upper end decoded. It is `none`
when one of these steps fails. -/
def upperEnd (B : Backend α) (e : Interval.Expr) (box : Box) : Option ℚ :=
  (box.enclose? B).bind fun intervals ↦
    (e.evalZero? B fun i ↦ intervals[i]?).bind fun I ↦ B.decode I.hi

/-- Whether an upper end passes the test of `relation`, the last step of `Expr.checkBoxZero`. -/
def passes (relation : Relation) : Option ℚ → Bool
  | some hi => relation.check hi
  | none => false

/-- Whether the upper end `a` is at least as far from passing as `b`: it is missing, or it is at
least `b`. -/
def worse : Option ℚ → Option ℚ → Bool
  | none, _ => true
  | some _, none => false
  | some a, some b => decide (b ≤ a)

/--
A refutation of the atom `fails relation e` on `box`, whose upper end `upperEnd B e box` is
`hi?`, with the evaluations of the budget `work` that are left. It is `atom 0` when `hi?` passes,
and otherwise the bisection of the coordinate that `choose` picks, at most `cuts` levels deep,
with both halves refuted. The half that is further from passing comes first (`worse`), so that a
bound that fails near a point is given up after about `2 * cuts` evaluations. Every evaluation of
a half spends one unit of `work`. The result is `none` when the work, the levels or the
coordinates run out first.
-/
def descend (B : Backend α) (choose : Box → Option ℕ) (relation : Relation)
    (e : Interval.Expr) : ℕ → Box → Option ℚ → ℕ → Option Refutation × ℕ
  | cuts, box, hi?, work =>
    if passes relation hi? then (some (.atom 0), work)
    else
      match cuts, choose box, work with
      | cuts + 1, some i, work + 2 =>
        match box.halve i with
        | none => (none, work + 2)
        | some (lower, upper) =>
          let lowerHi := upperEnd B e lower
          let upperHi := upperEnd B e upper
          let lowerFirst := worse lowerHi upperHi
          let (first, firstHi, second, secondHi) :=
            if lowerFirst then (lower, lowerHi, upper, upperHi)
            else (upper, upperHi, lower, lowerHi)
          match descend B choose relation e cuts first firstHi work with
          | (some r₁, work) =>
            match descend B choose relation e cuts second secondHi work with
            | (some r₂, work) =>
              (some (if lowerFirst then .bisect i r₁ r₂ else .bisect i r₂ r₁), work)
            | (none, work) => (none, work)
          | (none, work) => (none, work)
      | _, _, work => (none, work)
termination_by structural cuts _ _ _ => cuts

/-- A refutation of the atom `fails relation e` on `box` by the backend `B`, with the evaluations
of the budget `work` that are left: `descend` after one evaluation on the whole box. -/
def planAtom (B : Backend α) (choose : Box → Option ℕ) (relation : Relation)
    (e : Interval.Expr) (cuts : ℕ) (box : Box) : ℕ → Option Refutation × ℕ
  | 0 => (none, 0)
  | work + 1 => descend B choose relation e cuts box (upperEnd B e box) work

/--
A refutation of the constraint `c` on `box` by the backend `B`, with the evaluations of the
budget `work` that are left: an atom as `planAtom` refutes it, a disjunction by refutations of
both parts (`both`), each with its own bisections, and a conjunction by a refutation of its
first part (`left`) or else of its second (`right`). A form atom gets no refutation here.
-/
def plan (B : Backend α) (choose : Box → Option ℕ) (cuts : ℕ) :
    Constraint → Box → ℕ → Option Refutation × ℕ
  | .fails relation e, box, work => planAtom B choose relation e cuts box work
  | .form .., _, work => (none, work)
  | .and a b, box, work =>
    match plan B choose cuts a box work with
    | (some l, work) => (some (.left l), work)
    | (none, work) =>
      match plan B choose cuts b box work with
      | (some r, work) => (some (.right r), work)
      | (none, work) => (none, work)
  | .or a b, box, work =>
    match plan B choose cuts a box work with
    | (some l, work) =>
      match plan B choose cuts b box work with
      | (some r, work) => (some (.both l r), work)
      | (none, work) => (none, work)
    | (none, work) => (none, work)

/--
The coordinate of `box` that the sensitivity heuristic of the registry picks for `expr` at the
policy `precision` (`CertifiedEvalRegistry.selectVariableSubdivisionChoice?` on `boxRegistry`),
and otherwise the widest one (`Box.widest?`). Coordinate `i` of the CEGA box is interval `i` of
`box`, and an interval whose ends are out of order reads as its lower end. With one coordinate
there is nothing to choose, and the heuristic, which encloses a derivative, is not run.
-/
def sensitiveCoordinate {n : ℕ} (precision : Precision) (expr : Verified.Expr (Fin n))
    (box : Box) : Option ℕ :=
  let widest := box.widest?.map (·.1)
  if n ≤ 1 then widest
  else
    let intervals : Fin n → RationalInterval := fun i ↦
      match box[i.val]? with
      | some I => if h : I.lo ≤ I.hi then .ofFloatLib I h else .const I.lo
      | none => .const 0
    match (boxRegistry intervals precision).selectVariableSubdivisionChoice?
        (List.finRange n) expr with
    | some choice => some choice.coordinate.val
    | none => widest

end Refute

end CAS.CEGA

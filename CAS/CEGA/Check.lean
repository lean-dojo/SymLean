/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalEval.Context
public import CAS.Continuum.IntervalEval.Registry.Monotonicity
public import CAS.Expr.FloatLib
public import FloatLib.Numerics.Enclosure.Expression.BackendsProof
public import FloatLib.Numerics.Enclosure.Expression.Diagnose

/-!
# FloatLib's evaluations as CEGA queries

A goal of `cega` bounds an expression on a box with rational bounds, and FloatLib computes the
bound. This module joins the two. `Endpoints` is a backend of FloatLib with its soundness proof:
exact rationals, the binary grid, any outward rounding of FloatLib, or the backend of `cega`'s
certified evaluation context. `enclose?` rounds the box outward into the backend's endpoints,
evaluates the translation of the expression on it with FloatLib's zero rule (`Expr.evalZero?`),
and reads the two ends of the result back as rationals. It returns them as an `EnclosureAttempt`,
the record that every CEGA query returns, so the theorems of `CAS.CEGA.Query` that compare a
query with stated bounds (`enclosedOn_of_check`, `boundOn_of_check` and the others) take it as
they take the planner's queries. When there is no result, `obstruction?` says why, in the words of
FloatLib's diagnosis (`Expr.diagnose`). `holdsOn_of_checkZero` is the other way in: one Boolean
check by FloatLib, with FloatLib's own subdivision of the box, proves `expr ≤ 0` or `expr < 0` at
every point of the box.

## Main definitions

* `Endpoints`: a backend of FloatLib at each accuracy setting, with its soundness proof.
  `Endpoints.rational`, `Endpoints.binaryGrid`, `Endpoints.ofRounding` and `Endpoints.exact` are
  exact rationals, the binary grid, an outward rounding, and the backend of `cega`'s certified
  evaluation. `Endpoints.backend` adds FloatLib's standard calls: `π`, the real power and `e`.
* `toBox`, `toValues`: a CEGA box and a point of it, as FloatLib reads them.
* `enclose?`: the query.
* `obstruction?`: why the query has no result.

## Main results

* `Endpoints.backend_sound`: the backend with the standard calls is sound.
* `containsReal_toBox`: a point of the CEGA box is a point of FloatLib's box.
* `containsReal_eval_of_evalZero?`, `bounds_of_evalZero?`: a successful evaluation encloses the
  expression at every point of the box.
* `exists_of_enclose?`: the interval of a successful query is FloatLib's result, read as
  rationals.
* `obstruction?_eq_none_iff`: `obstruction?` reports nothing exactly when the query has a result.
* `holdsOn_of_checkZero`: a passing check proves its relation at every point of the box.

## Implementation notes

An `EnclosureAttempt` holds a `RationalInterval`, whose ends are ordered. FloatLib's result has
that order because it contains a real number, the value of the expression at the corner of the
lower bounds of the box, so no comparison of the two ends is evaluated. For the same reason the
reading back of a result never fails (`obstruction?_eq_none_iff`). Coordinate `i` of the box is
FloatLib's input `i` (`Verified.Expr.toFloatLib Fin.val`), so FloatLib's subdivision of the box
splits a coordinate everywhere it occurs.

This module loads FloatLib's numerics and none of its float formats, which `CAS.CEGA.FloatQuery`
adds, so that a module can name these queries without loading the formats.
-/

@[expose] public section

open FloatLib.Numerics hiding RationalInterval
open FloatLib.Numerics.Interval
open CAS.Continuum CAS.Continuum.RationalInterval

namespace CAS.CEGA.Check

/-- A backend of FloatLib for the ends of CEGA's intervals: their type, the backend at each
accuracy setting, and the proof that each successful operation of the backend encloses its real
result. -/
structure Endpoints where
  /-- The type of the ends of the intervals. -/
  Carrier : Type
  /-- The backend at the accuracy settings `config`, without registered calls. -/
  base : Backend.Config → Backend Carrier
  /-- Each successful operation of the backend encloses its real result. -/
  sound : ∀ config, (base config).Sound

namespace Endpoints

/-- Exact rational ends (`Backend.rational`). -/
def rational : Endpoints :=
  ⟨ℚ, fun config ↦ Backend.rational config, fun config ↦ Backend.rational_sound config⟩

/-- Ends that are integer multiples of `2 ^ (-config.precision)` (`Backend.binaryGrid`). -/
def binaryGrid : Endpoints :=
  ⟨Int, fun config ↦ Backend.binaryGrid config, fun config ↦ Backend.binaryGrid_sound config⟩

/-- The ends of the outward rounding `R`: each operation is computed in exact rationals and its
result rounded outward by `R` (`Backend.ofRounding`). -/
def ofRounding {α : Type} (R : OutwardRounding α ℚ) : Endpoints :=
  ⟨α, fun config ↦ Backend.ofRounding R config, fun config ↦ Backend.ofRounding_sound R config⟩

/-- The backend of `cega`'s certified evaluation at the precision policy `precision`
(`Precision.backend`): exact rational arithmetic, and FloatLib's elementary enclosures at the
policy's setting, rounded to about 128 significant bits. The accuracy settings of a query with
these ends set only its standard calls: `π`, the real power and `e`; `cega`'s evaluation context
uses `precision.toConfig`. -/
def exact (precision : Precision) : Endpoints :=
  ⟨ℚ, fun _ ↦ precision.backend, fun _ ↦ precision.backend_sound⟩

/-- The backend of `endpoints` at the accuracy settings `config`, with FloatLib's standard calls
`Backend.Standard.extensions` added: `π` is the call `0`, the real power the call `1` and `e`
the call `2`, as in `Verified.Expr.toFloatLib`. -/
def backend (endpoints : Endpoints) (config : Backend.Config) : Backend endpoints.Carrier :=
  (endpoints.base config).withExtensions config Backend.Standard.extensions

/-- The backend with the standard calls is sound, with the real functions
`Backend.Standard.functions` for its calls. -/
theorem backend_sound (endpoints : Endpoints) (config : Backend.Config) :
    (endpoints.backend config).Sound (extensionValues Backend.Standard.functions) :=
  Backend.withExtensions_sound (endpoints.sound config) config Backend.Standard.extensions_sound

end Endpoints

/-- The CEGA box `box` as a box of FloatLib, with its coordinates in order. -/
def toBox {n : ℕ} (box : Fin n → RationalInterval) : Box :=
  List.ofFn fun i ↦ (box i).toFloatLib

/-- The point `x` as FloatLib's real inputs: coordinate `i` at index `i`, and `0` at the indices
from `n` on, which no expression of `Verified.Expr (Fin n)` reads. -/
noncomputable def toValues {n : ℕ} (x : Fin n → ℝ) : ℕ → ℝ :=
  fun k ↦ if h : k < n then x ⟨k, h⟩ else 0

/-- `toValues x` holds coordinate `i` of `x` at index `i`. -/
@[simp] theorem toValues_val {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : toValues x i = x i := by
  simp [toValues]

/-- A point `x` of the CEGA box `box`, read by `toValues`, is a point of FloatLib's box
`toBox box`. -/
theorem containsReal_toBox {n : ℕ} {box : Fin n → RationalInterval} {x : Fin n → ℝ}
    (hx : ∀ i, (box i).MemReal (x i)) : (toBox box).ContainsReal (toValues x) := by
  intro k I hI
  rw [toBox, List.getElem?_ofFn] at hI
  split_ifs at hI with hk
  obtain rfl := Option.some.inj hI
  simpa [toValues, hk] using ((box ⟨k, hk⟩).toFloatLib_containsReal_iff _).mpr (hx ⟨k, hk⟩)

variable {n : ℕ} {endpoints : Endpoints} {config : Backend.Config}
  {box : Fin n → RationalInterval} {expr : Verified.Expr (Fin n)}

/-- A successful evaluation of `expr.toFloatLib Fin.val`, on the box `toBox box` rounded outward
into the ends of `endpoints`, contains the value of `expr` at every point `x` of the box. -/
theorem containsReal_eval_of_evalZero? {intervals : List (Interval endpoints.Carrier)}
    {I : Interval endpoints.Carrier}
    (hbox : (toBox box).enclose? (endpoints.base config) = some intervals)
    (heval : (expr.toFloatLib Fin.val).evalZero? (endpoints.backend config)
      (Kernel.Seq.nth? intervals) = some I)
    {x : Fin n → ℝ} (hx : ∀ i, (box i).MemReal (x i)) :
    I.ContainsReal (endpoints.base config).decode (expr.eval x) :=
  Verified.Expr.containsReal_evalZero? (endpoints.sound config) (toValues_val x)
    (fun k K hK ↦ Box.containsReal_enclose? (endpoints.sound config) hbox
      (containsReal_toBox hx) k K (by rwa [Kernel.Seq.nth?_eq] at hK)) expr heval

/-- The rational ends `J` of a successful evaluation bound `expr` at every point `x` of the box.
The result comes from three steps that succeeded: the box rounded outward into the ends of
`endpoints`, the evaluation of `expr.toFloatLib Fin.val` with the zero rule, and the reading of
its two ends as rationals. -/
theorem bounds_of_evalZero? {intervals : List (Interval endpoints.Carrier)}
    {I : Interval endpoints.Carrier} {J : Interval ℚ}
    (hbox : (toBox box).enclose? (endpoints.base config) = some intervals)
    (heval : (expr.toFloatLib Fin.val).evalZero? (endpoints.backend config)
      (Kernel.Seq.nth? intervals) = some I)
    (hdecode : I.decode? (endpoints.base config).decode = some J)
    {x : Fin n → ℝ} (hx : ∀ i, (box i).MemReal (x i)) :
    (J.lo : ℝ) ≤ expr.eval x ∧ expr.eval x ≤ J.hi :=
  (containsReal_iff_of_decode? hdecode _).mp (containsReal_eval_of_evalZero? hbox heval hx)

/--
The enclosure of `expr` on the box `box` that FloatLib computes with the backend of `endpoints`
at the accuracy settings `config`, as a CEGA query.

The box is rounded outward into the ends of `endpoints` (`Box.enclose?`), the translation
`expr.toFloatLib Fin.val` is evaluated on it with the zero rule (`Expr.evalZero?`), and the two
ends of the result are read as rationals. The attempt holds that interval and the proof that it
encloses `expr` at every point of the box (`bounds_of_evalZero?`). There is no attempt when a
bound of the box has no enclosure in the ends of `endpoints`, or when the backend rejects an
operation on the intervals it gets, such as a quotient by an interval that contains zero, a
logarithm of an interval that reaches zero, or a result past the largest number of a float
format. `obstruction?` says which.
-/
def enclose? (endpoints : Endpoints) (config : Backend.Config)
    (box : Fin n → RationalInterval) (expr : Verified.Expr (Fin n)) :
    Option (EnclosureAttempt (ℝ^n) (boxDomain box) (fun x ↦ expr.eval fun i ↦ x i)) :=
  match hbox : (toBox box).enclose? (endpoints.base config) with
  | none => none
  | some intervals =>
    match heval : (expr.toFloatLib Fin.val).evalZero? (endpoints.backend config)
        (Kernel.Seq.nth? intervals) with
    | none => none
    | some I =>
      match hdecode : I.decode? (endpoints.base config).decode with
      | none => none
      | some J =>
        have bounds := fun x hx ↦ bounds_of_evalZero? hbox heval hdecode (x := x) hx
        some
          { interval := ofFloatLib J (by
              have h := bounds (fun i ↦ ((box i).lo : ℝ)) fun i ↦ (box i).lo_memReal
              exact_mod_cast h.1.trans h.2)
            sound := fun x hx ↦ bounds (fun i ↦ x i) hx }

/-- The interval of a successful query is FloatLib's result read as rationals: the box has an
enclosure in the ends of `endpoints`, the evaluation on it gives `I`, and the two ends of `I` read
as those of the interval. -/
theorem exists_of_enclose?
    {a : EnclosureAttempt (ℝ^n) (boxDomain box) (fun x ↦ expr.eval fun i ↦ x i)}
    (h : enclose? endpoints config box expr = some a) :
    ∃ intervals I, (toBox box).enclose? (endpoints.base config) = some intervals ∧
      (expr.toFloatLib Fin.val).evalZero? (endpoints.backend config)
        (Kernel.Seq.nth? intervals) = some I ∧
      I.decode? (endpoints.base config).decode = some a.interval.toFloatLib := by
  unfold enclose? at h
  split at h
  · cases h
  · rename_i intervals hbox
    split at h
    · cases h
    · rename_i I heval
      split at h
      · cases h
      · rename_i J hdecode
        obtain rfl := Option.some.inj h
        exact ⟨intervals, I, hbox, heval, hdecode⟩

/-- Why `enclose? endpoints config box expr` has no result, in the words of FloatLib's diagnosis:
`none` when the query has a result. Otherwise it is `missingVariable i` when the bounds of
coordinate `i` of the box, the first such coordinate, have no enclosure in the ends of
`endpoints`, and else the first obstruction of FloatLib's evaluation of `expr` on the box
(`Expr.diagnose`): the first operation that the backend rejects, with its decoded inputs. -/
def obstruction? (endpoints : Endpoints) (config : Backend.Config)
    (box : Fin n → RationalInterval) (expr : Verified.Expr (Fin n)) : Option Obstruction :=
  match (toBox box).enclose? (endpoints.base config) with
  | none =>
    some (.missingVariable ((toBox box).findIdx fun I ↦
      ((endpoints.base config).encloseInterval? I).isNone))
  | some intervals =>
    ((expr.toFloatLib Fin.val).diagnose (endpoints.backend config)
      (Kernel.Seq.nth? intervals)).obstruction?

/-- **The diagnosis explains every query without a result.** `obstruction?` reports nothing
exactly when `enclose?` has a result. The reading of a result as rationals never fails: the
result contains the value of the expression at the corner of the lower bounds of the box. -/
theorem obstruction?_eq_none_iff :
    obstruction? endpoints config box expr = none ↔
      (enclose? endpoints config box expr).isSome = true := by
  constructor
  · intro h
    unfold enclose?
    split
    · rename_i hbox
      simp [obstruction?, hbox] at h
    · rename_i intervals hbox
      simp only [obstruction?, hbox] at h
      split
      · rename_i heval
        cases hd : (expr.toFloatLib Fin.val).diagnose (endpoints.backend config)
            (Kernel.Seq.nth? intervals) with
        | success I => cases heval.symm.trans (Expr.diagnose_eq_success_iff.mp hd)
        | failure o => simp [hd, Diagnosis.obstruction?] at h
      · rename_i I heval
        split
        · rename_i hdecode
          have hc := containsReal_eval_of_evalZero? hbox heval fun i ↦ (box i).lo_memReal
          cases hlo : (endpoints.base config).decode I.lo with
          | none =>
            obtain ⟨_, _, h, -⟩ := hc
            simp [hlo] at h
          | some a =>
            cases hhi : (endpoints.base config).decode I.hi with
            | none =>
              obtain ⟨_, _, -, h, -⟩ := hc
              simp [hhi] at h
            | some b =>
              rw [(Interval.decode?_eq_some_iff _ I ⟨a, b⟩).mpr ⟨hlo, hhi⟩] at hdecode
              cases hdecode
        · rfl
  · intro h
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨intervals, I, hbox, heval, -⟩ := exists_of_enclose? ha
    simp [obstruction?, hbox, Expr.diagnose_eq_success_iff.mpr heval, Diagnosis.obstruction?]

/-- A passing FloatLib check with the zero rule of `expr.toFloatLib Fin.val` on the box
`toBox box`, by the backend of `endpoints` at the accuracy settings `config`, proves `relation`
(`expr ≤ 0` or `expr < 0`) at every point of the CEGA box `box`. This is
`Verified.Expr.holds_of_checkZero` at the points of the box (`containsReal_toBox`). -/
theorem holdsOn_of_checkZero (endpoints : Endpoints) (config : Backend.Config)
    {relation : Relation} {depth : ℕ}
    (h : (expr.toFloatLib Fin.val).checkZero (endpoints.backend config) relation (toBox box)
      depth = true) :
    ∀ x ∈ boxDomain box, relation.Holds (expr.eval fun i ↦ x i) :=
  fun x hx ↦ Verified.Expr.holds_of_checkZero (endpoints.sound config)
    (toValues_val fun i ↦ x i) expr h (containsReal_toBox hx)

end CAS.CEGA.Check

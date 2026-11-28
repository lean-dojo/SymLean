/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.CEGA.Check
public import CAS.CEGA.Query
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Interval.Outward
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Codecs

/-!
# The CEGA box query in a floating-point format

How does a bound that the kernel computes with IEEE floats become a statement about real numbers
that `cega` can hand to its goal, by the same theorems as a bound computed with rationals?

FloatLib has the arithmetic. `ExecFloat.Binary.intervalRounding` rounds a rational outward to the
two nearest finite numbers of a binary format, and `Backend.ofRounding` makes it an interval
backend: each operation is computed in exact rationals and its result rounded outward into the
format. `Check.Endpoints.binary` is that backend, and the float query `encloseBoxFloat?` is
`Check.enclose?` on it, on each piece of a subdivision of the box, with the pieces joined by
`EnclosureAttempt.ofBinaryCover`. Its type is that of the planner's query `encloseBoxWith?`, so the
theorems that compare a query with stated bounds (`boundOn_of_check`, `enclosedOn_of_check` and
the others) and the transports of `cega` take a float query as they take a rational one. The
comparison with a stated bound is exact, because a float end is a rational number. When the query
has no result, `floatObstruction?` says why, in the words of FloatLib's diagnosis.

## Main definitions

* `floatConfig`: the accuracy settings of FloatLib's elementary enclosures for a format.
* `Check.Endpoints.binary`: the numbers of a binary format as the ends of intervals.
* `encloseBoxFloat?`: the query in a format, after a schedule of bisections. The empty schedule is
  the query on the whole box.
* `floatObstruction?`: why the query has no result.

## Main results

* `encloseBoxFloat?_isSome_iff` (all formats, schedules, boxes and expressions): the query has a
  result exactly when `floatObstruction?` reports nothing.
* `ends_of_encloseBoxFloat?` (the same scope): the two ends of the interval of a result are the
  values of finite numbers of the format.

## Implementation notes

FloatLib encloses a square root on a grid of `2 ^ (-precision)` and the other elementary
functions with series of `degree` terms, and only then rounds the result into the format. So
`floatConfig` gives the grid the format's significant bits and 16 guard bits, and raises the
degree with them. For binary128, whose 113 bits hold thirty digits of `√2`, that is a grid of 129
bits. The grid is absolute, so a square root of a tiny number keeps fewer significant bits than
the format has.

`CAS.CEGA.Elaboration` builds the query and its diagnosis by name, so that the certificate
framework and the `#cas` commands, which use that module for its kernel checks, do not load
FloatLib's float formats. `CAS.CEGA` imports this module, and with it every file that can call
`cega`.

## Scope

`encloseBoxFloat?` runs FloatLib's natural interval evaluation on each piece of a fixed
subdivision schedule. On ordinary inequalities the box tactic first tries a separate refutation
check, which can bisect adaptively in the same float format. The rational enclosure planner
also has monotonicity faces and centered forms, which prove a tight bound such as
`x * (1 - x) ≤ 1 / 4` on `[0, 1]`; in a float format such a bound is proved only with some room.
The quadrature of `CAS.CEGA.Integration` has no float form.

## References

* Ramon E. Moore, R. Baker Kearfott and Michael J. Cloud, *Introduction to Interval Analysis*,
  SIAM, Philadelphia, 2009, <https://doi.org/10.1137/1.9780898717716>. Chapter 3 for outward
  rounding, Chapter 6 for the refinement of an interval extension by subdivision.
* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, <https://github.com/lean-dojo/FloatLib>. The binary formats, their outward
  rounding and the interval backends.
-/

@[expose] public section

namespace CAS.CEGA

open CAS.Continuum CAS.Continuum.RationalInterval
open FloatLib.Numerics hiding RationalInterval
open FloatLib.Numerics.Interval
open FloatLib.Floats.Formats.BinaryInterchange

/-- The accuracy settings of FloatLib's elementary enclosures and standard calls for a query in
the format `format`. FloatLib computes the square root on a grid of `2 ^ (-precision)`, `π` to
within `2 ^ (-precision)` and `e` at the same precision, and the other functions with series of
`degree` terms, before it rounds the result into the format. So `precision` is the format's
`fracWidth + 1` significant bits and 16 guard bits, and the degree is two thirds of `precision`,
since the slowest series, that of the logarithm, gains about 1.6 bits a term. Binary64 gets 69
bits at degree 47, and binary128 129 bits at degree 87. -/
def floatConfig (format : FloatFormat) : Backend.Config :=
  let precision := format.fracWidth + 17
  { precision, degree := 2 * precision / 3 + 1 }

/-- The numbers of the binary floating-point format `format`, such as `FloatFormat.binary64`, as
the ends of intervals. Each operation is computed in exact rationals and its result rounded
outward to finite numbers of the format (`ExecFloat.Binary.intervalRounding`), so a result past
the largest finite number has no enclosure. The storage is `.wide`, FloatLib's model of the
format itself, which holds a format of any width. -/
def Check.Endpoints.binary (format : FloatFormat) : Check.Endpoints :=
  .ofRounding (FloatLib.Floats.ExecFloat.Binary.intervalRounding (format := format) (plan := .wide))

variable {n : ℕ}

/--
The enclosure of `expr` on the box `box`, computed with intervals of the binary format `fmt` after
the bisections of `schedule`: each coordinate of `schedule` in turn cuts every piece in two at its
midpoint (`bisectRationalBox`), FloatLib encloses `expr` on each piece (`Check.enclose?` with the
ends `Check.Endpoints.binary fmt` at the settings `floatConfig fmt`), and the pieces are joined by
`EnclosureAttempt.ofBinaryCover`. There is no attempt when a piece has none, and
`floatObstruction?` says why.

The enclosure holds in every format, since FloatLib's rounding checks each end it returns with
exact rationals. The proof `hfmt` keeps the query to the IEEE formats that `cega` accepts.
-/
noncomputable def encloseBoxFloat? (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    (schedule : List (Fin n)) → (box : Fin n → RationalInterval) →
      (expr : Verified.Expr (Fin n)) →
        Option (EnclosureAttempt (ℝ^n) (boxDomain box) (fun x ↦ expr.eval fun i ↦ x i))
  | [], box, expr => Check.enclose? (.binary fmt) (floatConfig fmt) box expr
  | coordinate :: schedule, box, expr =>
    let bisection := bisectRationalBox box coordinate
    match encloseBoxFloat? fmt hfmt schedule bisection.left expr,
        encloseBoxFloat? fmt hfmt schedule bisection.right expr with
    | some left, some right => some (EnclosureAttempt.ofBinaryCover bisection.cover left right)
    | _, _ => none

/-- Why `encloseBoxFloat? fmt hfmt schedule box expr` has no result, in the words of FloatLib's
diagnosis: `none` when it has one, and otherwise what `Check.obstruction?` reports for the first
piece without an enclosure, in the order of the bisections. On a piece, `missingVariable i` means
that a bound of coordinate `i` is past the largest finite number of the format, and
`rejected node inputs` that FloatLib rejected the operation at `node` on the intervals `inputs`: a
quotient by an interval that contains zero, a logarithm or a real power of an interval that is not
positive, or a result past the largest finite number. -/
def floatObstruction? (fmt : FloatFormat) :
    (schedule : List (Fin n)) → (box : Fin n → RationalInterval) →
      (expr : Verified.Expr (Fin n)) → Option Obstruction
  | [], box, expr => Check.obstruction? (.binary fmt) (floatConfig fmt) box expr
  | coordinate :: schedule, box, expr =>
    let bisection := bisectRationalBox box coordinate
    (floatObstruction? fmt schedule bisection.left expr).or
      (floatObstruction? fmt schedule bisection.right expr)

variable {fmt : FloatFormat} {hfmt : fmt.isIEEE = true} {schedule : List (Fin n)}
  {box : Fin n → RationalInterval} {expr : Verified.Expr (Fin n)}

/-- **A float query has a result exactly when its diagnosis reports nothing**, so
`floatObstruction?` explains every float query without a result. -/
theorem encloseBoxFloat?_isSome_iff :
    (encloseBoxFloat? fmt hfmt schedule box expr).isSome = true ↔
      floatObstruction? fmt schedule box expr = none := by
  induction schedule generalizing box with
  | nil => exact Check.obstruction?_eq_none_iff.symm
  | cons coordinate schedule ih =>
    rw [encloseBoxFloat?, floatObstruction?, Option.or_eq_none_iff, ← ih, ← ih]
    cases encloseBoxFloat? fmt hfmt schedule (bisectRationalBox box coordinate).left expr <;>
      cases encloseBoxFloat? fmt hfmt schedule (bisectRationalBox box coordinate).right expr <;>
      simp

/-- **The bounds of a float query are floats.** The two ends of the interval of a successful
query are the real values of two finite numbers of the format `fmt`. So the enclosure that `cega`
compares with a stated bound is a pair of numbers of the chosen format, which is what computing
in that format means. On one piece the ends are FloatLib's result read as rationals
(`Check.exists_of_enclose?`), and the hull of two pieces keeps an end of one of them on each
side. -/
theorem ends_of_encloseBoxFloat?
    {a : EnclosureAttempt (ℝ^n) (boxDomain box) (fun x ↦ expr.eval fun i ↦ x i)}
    (h : encloseBoxFloat? fmt hfmt schedule box expr = some a) :
    ∃ l u : Model fmt, Model.isFinite l = true ∧ Model.isFinite u = true ∧
      (a.interval.lo : ℝ) = Model.toReal l ∧ (a.interval.hi : ℝ) = Model.toReal u := by
  induction schedule generalizing box with
  | nil =>
    obtain ⟨_, I, -, -, hdecode⟩ := Check.exists_of_enclose? h
    obtain ⟨hlo, hhi⟩ := (Interval.decode?_eq_some_iff _ _ _).mp hdecode
    have hlo : Model.toRat? (FloatLib.Floats.ExecFloat.Binary.toModel I.lo) =
        some a.interval.lo := hlo
    have hhi : Model.toRat? (FloatLib.Floats.ExecFloat.Binary.toModel I.hi) =
        some a.interval.hi := hhi
    exact ⟨_, _, Model.Algebraic.isFinite_of_toRat?_eq_some hlo,
      Model.Algebraic.isFinite_of_toRat?_eq_some hhi,
      (Model.Algebraic.toReal_of_toRat?_eq_some hlo).symm,
      (Model.Algebraic.toReal_of_toRat?_eq_some hhi).symm⟩
  | cons coordinate schedule ih =>
    rw [encloseBoxFloat?] at h
    split at h
    · rename_i left right hleft hright
      obtain rfl := Option.some.inj h
      obtain ⟨l₁, u₁, hl₁, hu₁, hlo₁, hhi₁⟩ := ih hleft
      obtain ⟨l₂, u₂, hl₂, hu₂, hlo₂, hhi₂⟩ := ih hright
      obtain ⟨l, hl, hlo⟩ : ∃ l : Model fmt, Model.isFinite l = true ∧
          ((min left.interval.lo right.interval.lo : ℚ) : ℝ) = Model.toReal l := by
        rcases min_choice left.interval.lo right.interval.lo with hm | hm <;> rw [hm]
        exacts [⟨l₁, hl₁, hlo₁⟩, ⟨l₂, hl₂, hlo₂⟩]
      obtain ⟨u, hu, hhi⟩ : ∃ u : Model fmt, Model.isFinite u = true ∧
          ((max left.interval.hi right.interval.hi : ℚ) : ℝ) = Model.toReal u := by
        rcases max_choice left.interval.hi right.interval.hi with hm | hm <;> rw [hm]
        exacts [⟨u₁, hu₁, hhi₁⟩, ⟨u₂, hu₂, hhi₂⟩]
      exact ⟨l, u, hl, hu, (congrArg _ (hull_lo _ _)).trans hlo,
        (congrArg _ (hull_hi _ _)).trans hhi⟩
    · cases h

end CAS.CEGA

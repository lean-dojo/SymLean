/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Stated bounds proved by FloatLib's refutation check

A bound on a box, such as `x * (1 - x) ≤ 1 / 3` for `x ∈ [0, 1]`, holds when its negation has no
point in the box. That is what `cega` asks FloatLib first: it writes the negation of the stated
bounds as one FloatLib constraint, cuts the box until FloatLib's interval evaluation refutes the
constraint on every piece, and has the kernel check the cuts with FloatLib's
`Constraint.refutes`. The first section applies the theorems behind that check by hand, one for
each kind of bound, with the refutations written out. The second shows the tactic on a
two-sided bound, on a bound that both FloatLib's check and the planner of `CAS.CEGA.Query` prove,
on `x * (1 - x) ≤ 1 / 4`, which only the planner proves, and on a bound that is false. The
trace class `cega.refute` reports each check.
-/

@[expose] public section

namespace CAS.Examples.CEGA.Refute

open CAS.Certificate CAS.CEGA CAS.Continuum CAS.Continuum.RationalInterval

-- These examples are about the kernel profile, also when the library is built with native
-- checking.
set_option cega.nativeCertificates false
set_option linter.hashCommand false

/-! ## The theorems, by hand

The backend is that of `cega`'s certified evaluation at the default policy. A refutation is
`atom 0`, one evaluation on the whole box, or `bisect 0 (atom 0) (atom 0)`, one evaluation on each
half of `[0, 1]`, and a two-sided bound is refuted side by side (`both`). `decide +kernel` has the
kernel run FloatLib's check of the refutation. -/

/-- The box `[0, 1]`. -/
def unitBox : Fin 1 → RationalInterval := fun _ ↦ .ofBounds 0 1 (by norm_num)

/-- The expression `x * (1 - x)`. -/
def parabola : Verified.Expr (Fin 1) := .mul (.var 0) (.sub (.nat 1) (.var 0))

/-- The expression `x - 1 / 2`. -/
def shifted : Verified.Expr (Fin 1) := .sub (.var 0) (.rat 1 2)

/-- The backend of `cega`'s certified evaluation at the default policy, as the ends of FloatLib's
intervals. -/
def ends : Check.Endpoints := .exact {}

/-- The accuracy settings of its standard calls. -/
def settings : FloatLib.Numerics.Interval.Backend.Config := ({} : Precision).toConfig

/-- `boundOn_of_refutes`: on each half of `[0, 1]`, FloatLib's interval evaluation of
`x * (1 - x)` has the upper end `1 / 2`. -/
theorem parabola_le : BoundOn (fun x ↦ parabola.eval fun i ↦ x i) (boxDomain unitBox)
    ((1 / 2 : ℚ) : ℝ) :=
  boundOn_of_refutes ends settings (r := .bisect 0 (.atom 0) (.atom 0)) (1 / 2)
    (by decide +kernel)

/-- `lt_of_refutes`: on each half the upper end `1 / 2` is below `3 / 4`. -/
theorem parabola_lt : ∀ x ∈ boxDomain unitBox, parabola.eval (fun i ↦ x i) < ((3 / 4 : ℚ) : ℝ) :=
  lt_of_refutes ends settings (r := .bisect 0 (.atom 0) (.atom 0)) (3 / 4) (by decide +kernel)

/-- `le_of_refutes_lower`: on the whole box the lower end is `0`. -/
theorem nonneg_parabola : ∀ x ∈ boxDomain unitBox, ((0 : ℚ) : ℝ) ≤ parabola.eval fun i ↦ x i :=
  le_of_refutes_lower ends settings (r := .atom 0) 0 (by decide +kernel)

/-- `lt_of_refutes_lower`: and `0` is above `-1 / 4`. -/
theorem parabola_gt : ∀ x ∈ boxDomain unitBox, ((-1 / 4 : ℚ) : ℝ) < parabola.eval fun i ↦ x i :=
  lt_of_refutes_lower ends settings (r := .atom 0) (-1 / 4) (by decide +kernel)

/-- `enclosedOn_of_refutes`: a two-sided bound is the disjunction of the failures of its sides,
refuted part by part (`both`), the lower side on the whole box and the upper side on each half. -/
theorem parabola_mem : EnclosedOn (fun x ↦ parabola.eval fun i ↦ x i) (boxDomain unitBox)
    ((0 : ℚ) : ℝ) ((1 / 2 : ℚ) : ℝ) :=
  enclosedOn_of_refutes ends settings (r := .both (.atom 0) (.bisect 0 (.atom 0) (.atom 0)))
    0 (1 / 2) (by decide +kernel)

/-- `boundOn_abs_of_refutes`: `|x - 1 / 2|` is at most `1 / 2` on the whole box. -/
theorem abs_shifted_le : BoundOn (fun x ↦ |shifted.eval fun i ↦ x i|) (boxDomain unitBox)
    ((1 / 2 : ℚ) : ℝ) :=
  boundOn_abs_of_refutes ends settings (r := .atom 0) (1 / 2) (by decide +kernel)

/-- `abs_lt_of_refutes`: and below `1`. -/
theorem abs_shifted_lt : ∀ x ∈ boxDomain unitBox, |shifted.eval fun i ↦ x i| < ((1 : ℚ) : ℝ) :=
  abs_lt_of_refutes ends settings (r := .atom 0) 1 (by decide +kernel)

/-- `approxOn_of_refutes`: `x * (1 - x)` is within `1 / 4` of `1 / 4` on each half. -/
theorem parabola_approx : ApproxOn (fun x ↦ parabola.eval fun i ↦ x i)
    (fun _ ↦ ((1 / 4 : ℚ) : ℝ)) (boxDomain unitBox) ((1 / 4 : ℚ) : ℝ) :=
  approxOn_of_refutes ends settings (r := .bisect 0 (.atom 0) (.atom 0)) (1 / 4) (1 / 4)
    (by decide +kernel)

/--
info: 'CAS.Examples.CEGA.Refute.parabola_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms parabola_mem

/-! ## The tactic

Bare `cega` tries FloatLib's check before the planner. A goal that states its bounds with numerals
gets one constraint, and the trace counts the pieces of the box that the kernel checks. -/

/--
trace: [cega.refute] FloatLib check, stated bound ∈ [0, 1/3]: refuted on 7 boxes, checked by the kernel
-/
#guard_msgs in
set_option trace.cega.refute true in
/-- A two-sided bound: one piece for the lower side and six for the upper side. -/
theorem two_sided (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ x * (1 - x) ∧ x * (1 - x) ≤ 1 / 3 := by
  cega

/--
info: 'CAS.Examples.CEGA.Refute.two_sided' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms two_sided

/--
trace: [cega.refute] FloatLib check, stated bound ≤ 1/3: refuted on 6 boxes, checked by the kernel
-/
#guard_msgs in
set_option trace.cega.refute true in
/-- A bound that FloatLib's check proves, on six pieces of the box. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 3 := by
  cega

/-- The explicit query proves the same bound without FloatLib's check, by the planner. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 3 := by
  cega [enclose x in [0, 1]] (x * (1 - x))

/--
trace: [cega.refute] FloatLib check, stated bound ≤ 1/4: no refutation within 4096 box evaluations and 32 cuts along a branch
-/
#guard_msgs in
set_option trace.cega.refute true in
/-- The bound is attained at `x = 1 / 2`, where every piece of the box that FloatLib evaluates has
an upper end above `1 / 4`: the check gives up after its 32 cuts toward that point, and the
planner proves the bound with its monotonicity faces. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  cega

/-- Neither has the monotonicity and centered forms of the exact planner. -/
#guard_msgs (substring := true, whitespace := lax) in
/-- In binary64 there is no planner, so `cega` refuses the same bound, and says why. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  cega (arith := binary64)

/-- comparison with the stated bound: the certified value does not give the stated bound. -/
#guard_msgs (substring := true, whitespace := lax) in
/-- A false bound: `x ^ 2` reaches `1` on `[0, 1]`. Both routes fall short, and the refusal names
the value the planner certifies and the limits of FloatLib's check. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x ^ 2 ≤ 1 / 2 := by
  cega

end CAS.Examples.CEGA.Refute

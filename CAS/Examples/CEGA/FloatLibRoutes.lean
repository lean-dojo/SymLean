/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.KernelPath

/-!
# The routes of bare `cega`, one goal each

Bare `cega` tries its routes in a fixed order: a checked carrier, `float_decide`, the quadrature
of an interval integral, a certificate goal, the box route, FloatLib's `interval`,
`dyadic_interval` on a closed goal, and a kernel certificate. Each route reads the shape of the
goal first and runs only when the shape fits. Below is one goal for each route, followed by the
axioms of its proof, then the shapes that the interval route reads, the suggestions of `cega?`
after the two FloatLib routes, and last the refusals.

Two of the routes are FloatLib's. `float_decide` decides a closed statement about floats in the
kernel, after FloatLib's kernel rules have rewritten its float operations, and `interval` proves
the inequalities that the box route cannot read, a bound on a finite sum for instance, as well
as bounds over a whole domain.
-/

@[expose] public section

namespace CAS.Examples.CEGA.FloatLibRoutes

open CAS.Certificate
open FloatLib.Floats

set_option linter.hashCommand false

/-! ## One goal for each route -/

/-- The carrier route projects a certificate of the local context. -/
theorem carrier_route (c : EnclosureCert ℝ (Set.Icc (0 : ℝ) 1)) :
    EnclosedOn c.fn (Set.Icc 0 1) c.lo c.hi := by
  cega

/-- info: 'CAS.Examples.CEGA.FloatLibRoutes.carrier_route' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms carrier_route

/-- The float_decide route decides a closed statement about binary64 values. -/
theorem float_route : (1.5 : Binary64) * 2.25 - 1 / 3 = 3.0416666666666665 := by
  cega

/-- info: 'CAS.Examples.CEGA.FloatLibRoutes.float_route' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms float_route

/-- The integral route proves a bound on an interval integral with checked quadrature panels. -/
theorem integral_route : |(∫ x in (0 : ℝ)..1, x ^ 2) - 1 / 3| ≤ 1 / 100 := by
  cega

/-- info: 'CAS.Examples.CEGA.FloatLibRoutes.integral_route' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_route

/-- The certificate route unfolds a certificate goal on a coordinate box. -/
theorem certificate_route : BoundOn (fun p : ℝ^1 ↦ |p 0 - 2|) {p | 0 ≤ p 0 ∧ p 0 ≤ 1} 3 := by
  cega

/-- info: 'CAS.Examples.CEGA.FloatLibRoutes.certificate_route' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms certificate_route

/-- The box route proves an ordinary inequality on bounded variables. Its maximum `1 / 4` is
reached inside the box, so no subdivision proves it and the planner's monotonicity faces do. -/
theorem box_route (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  cega

/-- info: 'CAS.Examples.CEGA.FloatLibRoutes.box_route' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms box_route

/-- The interval route proves a bound on a finite sum, which the box route reads as a single
variable without bounds. -/
theorem interval_route (x : Fin 3 → ℝ) (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    ∑ i, x i ^ 2 ≤ 3 := by
  cega

/-- info: 'CAS.Examples.CEGA.FloatLibRoutes.interval_route' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms interval_route

/-- The dyadic_interval route proves a closed disjunction, which no other route reads. -/
theorem dyadic_route : Real.pi < 3.14 ∨ Real.pi < 3.15 := by
  cega

/-- info: 'CAS.Examples.CEGA.FloatLibRoutes.dyadic_route' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dyadic_route

/-- The kernel certificate decides a closed statement about integers: the float_decide route does
not take it, since it mentions no float. -/
theorem certificate_check : ∀ i : Fin 8, (i.val : ℤ) ^ 2 < 64 := by
  cega

/-- info: 'CAS.Examples.CEGA.FloatLibRoutes.certificate_check' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms certificate_check

/-! ## The shapes of the interval route

The interval route takes a relation `≤`, `<`, `≥` or `>` between real or nonnegative real
numbers, a conjunction of them once the leading binders are introduced, or a bound over a whole
domain, which `interval` reads as it is. -/

/-- A bound over a whole domain: the coefficients of a trigonometric polynomial bound it for
every `u`, with no box. -/
theorem whole_domain : ∀ u : ℝ, Real.cos u + Real.cos (2 * u) / 2 ≤ 3 / 2 := by
  cega

/-- info: 'CAS.Examples.CEGA.FloatLibRoutes.whole_domain' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms whole_domain

/-- A bound on the unit circle, from the coefficients of a polynomial in `z`. -/
theorem unit_circle : ∀ z : ℂ, ‖z‖ = 1 → ‖z ^ 2 + 1‖ ≤ 2 := by
  cega

/-- info: 'CAS.Examples.CEGA.FloatLibRoutes.unit_circle' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unit_circle

/-- A bound under `∀ x ∈ Set.Icc lo hi`, which `interval` proves on that box. -/
theorem on_interval : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∑ i : Fin 3, (x + i) ^ 2 ≤ 14 := by
  cega

/-- info: 'CAS.Examples.CEGA.FloatLibRoutes.on_interval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms on_interval

/-- A conjunction under leading binders: the route introduces them and proves each relation. -/
theorem conjunction : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∑ i : Fin 2, (x + i) ^ 2 ≤ 5 ∧ 0 ≤ x * x := by
  cega

/-- info: 'CAS.Examples.CEGA.FloatLibRoutes.conjunction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms conjunction

/-- A strict bound written with `>`. -/
theorem greater (x : Fin 2 → ℝ) (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) : 3 > ∑ i, x i ^ 2 := by
  cega

/-- info: 'CAS.Examples.CEGA.FloatLibRoutes.greater' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms greater

/-- A nonnegative real inequality, which the box route does not read. -/
theorem nonnegative (x : NNReal) (h : x ≤ 1) : x * x ≤ 1 := by
  cega

/-- info: 'CAS.Examples.CEGA.FloatLibRoutes.nonnegative' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nonnegative

/-! ## The suggestions of `cega?`

After the two FloatLib routes, `cega?` suggests the FloatLib call that ran. -/

/--
info: Try this:
  [apply] float_decide

Lean checked the suggested replacement against the original goal. Selected route: CEGA route: kernel evaluation of a closed statement about floats (float_decide).
-/
#guard_msgs in
example : (1.5 : Binary64) + 2.25 = 3.75 := by
  cega?

/--
info: Try this:
  [apply] interval

Lean checked the suggested replacement against the original goal. Selected route: CEGA route: interval evaluation of a real inequality (FloatLib's interval), arithmetic: exact rationals.
-/
#guard_msgs in
example (x : Fin 3 → ℝ) (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) : ∑ i, x i ^ 2 ≤ 3 := by
  cega?

/-! ## Refusals

A route whose shape fits leads the refusal; the other routes follow it. -/

-- A false statement about floats: the float_decide route leads, and the kernel certificate,
-- which would decide the same statement without FloatLib's kernel rules, is not tried.
/--
error: cega float_decide route: the kernel did not evaluate
  1.5 + 2.25 = 3.5
to `true` after FloatLib's kernel rules rewrote its float operations. The statement may be false;
`float_decide` on its own says whether it is.
-/
#guard_msgs (error, substring := true, whitespace := lax) in
example : (1.5 : Binary64) + 2.25 = 3.5 := by
  cega

-- In a float arithmetic `interval`, which computes with exact rationals, is not run, and on a
-- finite sum its refusal leads.
/--
error: cega interval route: FloatLib's `interval` computes with exact rationals, so it is not run
in binary64 arithmetic. `cega [use_floats := false]` runs it.
-/
#guard_msgs (error, substring := true, whitespace := lax) in
example (x : Fin 3 → ℝ) (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) : ∑ i, x i ^ 2 ≤ 3 := by
  cega [use_floats]

-- A goal that no route reads: an equation of natural numbers with a free variable.
/-- error: This goal has the head symbol `Eq`; its outer shape is not supported by these routes. -/
#guard_msgs (error, substring := true, whitespace := lax) in
example (n : ℕ) : n + 0 = n := by
  cega

end CAS.Examples.CEGA.FloatLibRoutes

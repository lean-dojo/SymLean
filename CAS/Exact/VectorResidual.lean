/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Exact.ZeroResidual

/-!
# Vector symbolic residuals

A `VectorResidual n m` is a family of `m` symbolic residual components over `ℝ^n`, with a
constructor for an identity (`ofDifference`). Each component is checked by a scalar route. When
every component route ends at syntactic zero, the component results assemble into equality with
zero (`eqOn_zero`), a zero-error certificate (`vectorResidualCertZero`), and a vector-valued
zero residual bound (`residualBound_zero`). The variants `eqOn_zero_ready`,
`vectorResidualCertZeroReady` and `residualBound_zero_ready` use the unconditional `cas` route,
which emits no side obligations; the others use the side-conditioned route and take the domain
proofs of its obligations as hypotheses.
-/

@[expose] public section

namespace CAS

namespace Exact

open MeasureTheory
open CAS.Certificate

/-! ### Componentwise vector residuals

Vector PDE identities reduce to scalar identities in each component, so a `VectorResidual`
stores exactly those symbolic component expressions, and every vector statement is assembled
from the scalar checks of its components.
-/

/-- A finite family of symbolic residual components over an `n`-dimensional input. -/
def VectorResidual (n m : Nat) :=
  Fin m → Verified.Expr (Fin n)

namespace VectorResidual

/-- Build a vector residual for an identity `component = expected`.

Each component is normalized as `component i - expected i`, so the resulting route can be fed
directly to the componentwise proof constructors when the identity closes symbolically. -/
def ofDifference {n m : Nat}
    (component expected : Fin m → Verified.Expr (Fin n)) : VectorResidual n m :=
  fun i ↦ Verified.Expr.Alg.normalize (component i - expected i)

/-- The exact symbolic route for one component of the vector residual. -/
def componentRoute {n m : Nat} (route : VectorResidual n m)
    (i : Fin m) : SymbolicClaimRoute n :=
  SymbolicClaimRoute.cas (route i)

/-- The side-conditioned symbolic route for one component of the vector residual. -/
def componentSideRoute {n m : Nat} (route : VectorResidual n m)
    (i : Fin m) : SymbolicClaimRoute n :=
  SymbolicClaimRoute.withSideConditions (route i)

/-- Interpret a symbolic vector residual as a real vector-valued function. -/
noncomputable def vectorFn {n m : Nat} (route : VectorResidual n m) :
    ℝ^n → Fin m → ℝ :=
  fun x i ↦ (route i).eval x

/-- Component-level side-condition discharge predicate. -/
def ComponentSideHoldsOn {n m : Nat} (route : VectorResidual n m)
    (i : Fin m) (s : Set (ℝ^n)) : Prop :=
  (route.componentSideRoute i).SideHoldsOn s

/-- If the `cas` route of a component (`componentRoute`) ends at syntactic zero, that component
is zero on every patch. -/
theorem component_eqOn_zero_ready {n m : Nat} (route : VectorResidual n m)
    (s : Set (ℝ^n)) (i : Fin m)
    (hzero : (route.componentRoute i).rhs = (0 : Verified.Expr (Fin n))) :
    Set.EqOn (exprFn (route i)) zeroFn s := by
  simpa [componentRoute] using
    (route.componentRoute i).eqOn_zero_ready s hzero rfl

/-- If the side-conditioned route of a component (`componentSideRoute`) ends at syntactic zero,
that component is zero on any patch where the side obligations of the route hold. -/
theorem component_eqOn_zero {n m : Nat} (route : VectorResidual n m)
    (s : Set (ℝ^n)) (i : Fin m)
    (hside : route.ComponentSideHoldsOn i s)
    (hzero : (route.componentSideRoute i).rhs = (0 : Verified.Expr (Fin n))) :
    Set.EqOn (exprFn (route i)) zeroFn s := by
  simpa [componentSideRoute, ComponentSideHoldsOn] using
    (route.componentSideRoute i).eqOn_zero s hside hzero

/-- If the `cas` route of every component ends at syntactic zero, the whole vector residual is
zero on every patch. -/
theorem eqOn_zero_ready {n m : Nat} (route : VectorResidual n m)
    (s : Set (ℝ^n))
    (hzero : ∀ i : Fin m, (route.componentRoute i).rhs = (0 : Verified.Expr (Fin n))) :
    Set.EqOn route.vectorFn (fun _ ↦ 0) s := by
  intro x hx
  funext i
  simpa [vectorFn, exprFn, zeroFn] using route.component_eqOn_zero_ready s i (hzero i) hx

/-- If the side-conditioned route of every component ends at syntactic zero, the whole vector
residual is zero on any patch where the side obligations of every component route hold. -/
theorem eqOn_zero {n m : Nat} (route : VectorResidual n m)
    (s : Set (ℝ^n))
    (hside : ∀ i : Fin m, route.ComponentSideHoldsOn i s)
    (hzero : ∀ i : Fin m, (route.componentSideRoute i).rhs = (0 : Verified.Expr (Fin n))) :
    Set.EqOn route.vectorFn (fun _ ↦ 0) s := by
  intro x hx
  funext i
  simpa [vectorFn, exprFn, zeroFn] using route.component_eqOn_zero s i (hside i) (hzero i) hx

/-- The zero-error certificate for the whole vector residual on any patch, when the `cas` route
of every component ends at syntactic zero. -/
noncomputable def vectorResidualCertZeroReady {n m : Nat} (route : VectorResidual n m)
    (s : Set (ℝ^n))
    (hzero : ∀ i : Fin m, (route.componentRoute i).rhs = (0 : Verified.Expr (Fin n))) :
    ResidualCert (ℝ^n) (Fin m → ℝ) s :=
  ResidualCert.ofEqOnZero route.vectorFn
    (route.eqOn_zero_ready s hzero)

/-- If the `cas` route of every component ends at syntactic zero, the vector residual satisfies
the zero residual bound on every patch. -/
theorem residualBound_zero_ready {n m : Nat} (route : VectorResidual n m)
    (s : Set (ℝ^n))
    (hzero : ∀ i : Fin m, (route.componentRoute i).rhs = (0 : Verified.Expr (Fin n))) :
    ResidualBound route.vectorFn s 0 :=
  (route.vectorResidualCertZeroReady s hzero).sound

/-- The zero-error certificate for the whole vector residual on a patch where the side
obligations of every component route hold, when the side-conditioned route of every component
ends at syntactic zero. -/
noncomputable def vectorResidualCertZero {n m : Nat} (route : VectorResidual n m)
    (s : Set (ℝ^n))
    (hside : ∀ i : Fin m, route.ComponentSideHoldsOn i s)
    (hzero : ∀ i : Fin m, (route.componentSideRoute i).rhs = (0 : Verified.Expr (Fin n))) :
    ResidualCert (ℝ^n) (Fin m → ℝ) s :=
  ResidualCert.ofEqOnZero route.vectorFn
    (route.eqOn_zero s hside hzero)

/-- If the side-conditioned route of every component ends at syntactic zero, the vector residual
satisfies the zero residual bound on any patch where the side obligations of every component
route hold. -/
theorem residualBound_zero {n m : Nat} (route : VectorResidual n m)
    (s : Set (ℝ^n))
    (hside : ∀ i : Fin m, route.ComponentSideHoldsOn i s)
    (hzero : ∀ i : Fin m, (route.componentSideRoute i).rhs = (0 : Verified.Expr (Fin n))) :
    ResidualBound route.vectorFn s 0 :=
  (route.vectorResidualCertZero s hside hzero).sound

end VectorResidual

end Exact

end CAS

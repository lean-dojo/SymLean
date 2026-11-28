/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Scalar.Conditions
public import CAS.Domain.SideConditions

/-!
# Symbolic expression side conditions

Exact simplification of a `Verified.Expr (Fin n)` is valid only where the denominators and
other singular subexpressions it cancels are nonzero, and the closed-form pipelines return each
claim (`Verified.Expr.SideClaimRoute`) with the list of expressions that must not vanish. We
read an expression as the function `exprFn expr : ℝ^n → ℝ`, so that one such obligation on a
patch `s ⊆ ℝ^n` becomes the statement `NonzeroOn (exprFn expr) s` of real analysis, and an
expression paired with a proof of it is a certificate for the obligation.

## Main definitions

* `exprFn`: the real-valued function on `ℝ^n` defined by a symbolic expression.
* `ExprNonzeroCert n s`: an expression paired with a proof that it does not vanish on `s`.

## Implementation notes

Nothing is assumed by default: every certificate carries its proof. The real-root module
`CAS.Polynomial.RealRoot.ClosedForm` builds certificates from root-free rational intervals
(`CAS.Polynomial.RealRoot.exprNonzeroCertOfPolynomialRootFree`).
-/

@[expose] public section

namespace CAS
namespace Exact

open CAS.Domain

/-- Interpret a Euclidean symbolic expression as a real-valued function. -/
noncomputable def exprFn {n : Nat} (expr : Verified.Expr (Fin n)) : ℝ^n → ℝ :=
  fun x ↦ expr.eval fun i ↦ x i

/-- `exprFn` sends a syntactic difference to the pointwise difference of evaluations. -/
@[simp]
theorem exprFn_sub {n : Nat} (a b : Verified.Expr (Fin n)) :
    exprFn (a - b) =
      fun x : ℝ^n ↦ a.eval (fun i ↦ x i) - b.eval (fun i ↦ x i) :=
  rfl

/-- The zero function on symbolic Euclidean points. -/
def zeroFn {n : Nat} : ℝ^n → ℝ :=
  fun _ ↦ 0

/-- Unfolding lemma for `zeroFn`: it is the constant function `0` on `ℝ^n`. -/
@[simp] theorem zeroFn_eq {n : Nat} :
    (zeroFn : ℝ^n → ℝ) = fun _ ↦ 0 :=
  rfl

/-! ## Expression-level side-condition certificates -/

/-- A checked nonzero certificate for a concrete symbolic expression on a patch.

Unlike `NonzeroOn`, which concerns an arbitrary real function, this subtype records the
verified expression itself, in the form in which exact symbolic routes emit denominator and
singularity obligations. -/
abbrev ExprNonzeroCert (n : Nat) (s : Set (ℝ^n)) :=
  { expr : Verified.Expr (Fin n) // NonzeroOn (exprFn expr) s }

namespace ExprNonzeroCert

/-- The symbolic expression certified nonzero on the patch. -/
abbrev expr {n : Nat} {s : Set (ℝ^n)}
    (cert : ExprNonzeroCert n s) : Verified.Expr (Fin n) :=
  cert.1

/-- The expression does not vanish on `s`. -/
theorem sound {n : Nat} {s : Set (ℝ^n)}
    (cert : ExprNonzeroCert n s) :
    NonzeroOn (exprFn cert.expr) s :=
  cert.2

end ExprNonzeroCert

end Exact
end CAS

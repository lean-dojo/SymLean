/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Cert.Shard
public meta import CAS.Cert.Shard
public import CAS.Expr.RationalEvaluation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.OfScientific

/-!
# Reducing a structure of conditions to the fields that a computation cannot decide

## Motivation

The hypothesis of a computer-assisted theorem is often a tree of structures whose fields are
propositions: some are inequalities between numbers of the data, others are integrals, bounds at
every point of a continuous set, or regularity facts. For given data, which fields does a
computation decide, and what is then left to prove?

## The idea

`cert_cond` reads the goal as a condition of the language of [Cond](Cond.lean): a relation
`a ≤ b`, `a < b` or `a = b` between real expressions, a conjunction or a disjunction of such,
or a statement for every real `x` of an interval, `∀ x, lo ≤ x → x ≤ hi → …` or
`∀ x ∈ Set.Icc lo hi, …`, nested to any depth. It writes the condition with a proof that the
condition says what the goal says, and evaluates its test by `cert_eval`. `cert_scalar` is the
case of one relation between closed expressions; when the comparison of balls fails and both
sides are rational, it compares their exact values (`ratTest`). `cert_decide` extends both to
`≠` and bounded quantifiers over `Fin n`. `cert_fields` applies the constructor of a structure,
tries a closing tactic (by default `cert_decide`) on every field and keeps the fields on which
it fails; a field that stays open and is again a structure of conditions is split in the same
way. `cert_reduce name : S` turns the result into a theorem whose hypotheses are the open
fields.

Nothing is assumed about the structure or about the closing tactic, so the same command serves
every structure of conditions and every checker.

## Main results

* `holds_closed` (all conditions without data, all precisions): a passing test proves the
  condition, for every value of the cell variables.
* `Reify.condLe`, `condLt`, `condEq`, `condAnd`, `condOr`, `condIcc`, `condIccMem`: a condition
  that holds proves the statement it was read from, one lemma for each form of statement.
* `rel_of_ratTest` (all closed rational expressions, all relations decided on `ℚ`): a passing
  comparison of the exact rational values proves the relation; `le_of_ratTest`, `lt_of_ratTest`
  and `eq_of_ratTest` are its three cases.
* `cert_cond`, `cert_scalar`, `cert_decide` (tactics): for relations between real numbers,
  their finite combinations, and statements on intervals and boxes. They prove what the kernel
  (or, when `cega.nativeCertificates` is set, compiled code) accepts and fail otherwise.
* `cert_fields` (a tactic, for every goal that is a structure) and `cert_reduce name : S`
  (a command, for every structure `S` that is a closed proposition, without universe
  parameters, with independent fields): close the fields that the closing tactic decides and
  return the others, as goals or as the hypotheses of the theorem `name : (open fields) → S`.
  With `(leaving := [f, g])` the command fails unless the open fields are exactly these.

## Relations

`holds_closed` is `Cond.holds_of_run` ([Cond](Cond.lean)) for data indexed by `Empty`, so every
proof of `cert_cond`, and of `cert_scalar` by balls, is one application of the soundness theorem
of conditions. `rel_of_ratTest` is `Expr.evalRat?_sound`
([RationalEvaluation](../Expr/RationalEvaluation.lean)) at both sides; `cert_scalar` uses it
when the balls do not decide. The commands are the
general forms of `nscert_scalar`, `nscert_fields` and `nscert_reduce` of BlowupZoo's NSCert, with
`CAS.Verified.Expr` and the balls in place of `NSCert.Ex` and `NSCert.IV`, with the closing
tactic as a parameter, and with intervals and boxes in place of one polynomial on a rectangle
(`NSCert.Poly.subdiv`). [Leaves](Leaves.lean) lists the leaf conditions of a statement without
proving anything. [Structure](../Examples/Cert/Structure.lean) runs `cert_reduce` and
`#cert_leaves` on one structure, and `tests/cert/Refusals.lean` calls `cert_scalar`, `cert_cond`
and `cert_fields` directly.

`reify` here is a second reader of real terms next to `CAS.Elaboration.RealExpression.reify`
([RealExpression](../Elaboration/RealExpression.lean)), the traversal that `cas` and `cega`
share. That one returns the expression for a box of coordinates and reads `tan`, the hyperbolic
functions and integer powers as well. This one returns the expression with a proof that it
denotes the term, numbers the interval variables as cell variables, reads `max` and `min`, and
unfolds definitions and projections.

## Scope

The tests are sound and not complete. An equality, or an inequality between equal numbers, is
decided only when both sides are computed exactly: on the binary grid, or as rational numbers
without square roots, absolute values, `π` and elementary functions. The expressions must be
closed up to the interval variables: a field about data that are variables of the statement is
written as a `Cond` over an environment, as in [MeshSpec](../Examples/Cert/MeshSpec.lean). An
interval is cut in two at the center of its ball, rounded to the grid, at most `depth` times,
one variable at a time.
-/

@[expose] public section

namespace CAS.Cert

open CAS.Numerics CAS.Verified

/-! ### Conditions without data -/

/-- The cell variables of a statement without interval variables: every one is `0`. -/
def Reify.noCells : ℕ → ℝ := fun _ ↦ 0

/-- **Conditions without data.** If the test of a condition `c` that reads no data passes, then
`c` holds, for every value `σ` of its free cell variables. Every proof of `cert_cond` is one
application of this theorem. -/
theorem holds_closed (P : ℕ) (c : Cond Empty) (σ : ℕ → ℝ) (h : c.run P Empty.elim = true) :
    c.holds Empty.elim σ :=
  Cond.holds_of_run (fun i ↦ i.elim) c σ h

/-- The exact test of a relation `r` on `ℚ` between two closed expressions: both have a
rational value (`Expr.evalRat?`) and `r` holds between the two values. -/
def ratTest (r : ℚ → ℚ → Bool) (a b : Expr (Empty ⊕ ℕ)) : Bool :=
  match Expr.evalRat? (fun _ ↦ 0) a, Expr.evalRat? (fun _ ↦ 0) b with
  | some p, some q => r p q
  | _, _ => false

/-- **Exact comparison.** Let `r` be a test on `ℚ` that proves the relation `R` between the
casts of its arguments. If `ratTest r a b` passes, then `R x y` holds for the real numbers `x`
and `y` that the closed expressions `a` and `b` denote. This decides what balls cannot: an
equality, or an inequality between equal numbers, of rational expressions off the binary
grid. -/
theorem rel_of_ratTest {r : ℚ → ℚ → Bool} {R : ℝ → ℝ → Prop}
    (hr : ∀ p q : ℚ, r p q = true → R p q) {a b : Expr (Empty ⊕ ℕ)} {x y : ℝ}
    (ha : a.eval (Sum.elim Empty.elim Reify.noCells) = x)
    (hb : b.eval (Sum.elim Empty.elim Reify.noCells) = y) (h : ratTest r a b = true) :
    R x y := by
  have henv : (fun _ : Empty ⊕ ℕ ↦ (((0 : ℚ) : ℚ) : ℝ)) = Sum.elim Empty.elim Reify.noCells := by
    funext i
    cases i with
    | inl i => exact i.elim
    | inr k => simp [Reify.noCells]
  unfold ratTest at h
  split at h
  · rename_i p q hp hq
    have h1 := Expr.evalRat?_sound _ hp
    have h2 := Expr.evalRat?_sound _ hq
    rw [henv] at h1 h2
    rw [← ha, ← hb, h1, h2]
    exact hr p q h
  · exact absurd h (by simp)

/-- If the exact rational values of `a` and `b` satisfy `≤`, then `x ≤ y`. -/
theorem le_of_ratTest {a b : Expr (Empty ⊕ ℕ)} {x y : ℝ}
    (ha : a.eval (Sum.elim Empty.elim Reify.noCells) = x)
    (hb : b.eval (Sum.elim Empty.elim Reify.noCells) = y)
    (h : ratTest (fun p q ↦ decide (p ≤ q)) a b = true) : x ≤ y :=
  rel_of_ratTest (R := (· ≤ ·)) (fun _ _ hpq ↦ Rat.cast_le.mpr (of_decide_eq_true hpq)) ha hb h

/-- If the exact rational values of `a` and `b` satisfy `<`, then `x < y`. -/
theorem lt_of_ratTest {a b : Expr (Empty ⊕ ℕ)} {x y : ℝ}
    (ha : a.eval (Sum.elim Empty.elim Reify.noCells) = x)
    (hb : b.eval (Sum.elim Empty.elim Reify.noCells) = y)
    (h : ratTest (fun p q ↦ decide (p < q)) a b = true) : x < y :=
  rel_of_ratTest (R := (· < ·)) (fun _ _ hpq ↦ Rat.cast_lt.mpr (of_decide_eq_true hpq)) ha hb h

/-- If the exact rational values of `a` and `b` are equal, then `x = y`. -/
theorem eq_of_ratTest {a b : Expr (Empty ⊕ ℕ)} {x y : ℝ}
    (ha : a.eval (Sum.elim Empty.elim Reify.noCells) = x)
    (hb : b.eval (Sum.elim Empty.elim Reify.noCells) = y)
    (h : ratTest (fun p q ↦ decide (p = q)) a b = true) : x = y :=
  rel_of_ratTest (R := (· = ·)) (fun _ _ hpq ↦ congrArg _ (of_decide_eq_true hpq)) ha hb h

/-! ### Reification

Each lemma says that an expression denotes a real term when its parts do. `reify` applies
them from the leaves up, so the proof that an expression denotes the term has the size of the
term and contains no computation. -/

namespace Reify

variable {ι : Type*} {ρ : ι → ℝ} {a b : Expr ι} {x y : ℝ}

/-- A sum: if `a` denotes `x` and `b` denotes `y`, then `Expr.add a b` denotes `x + y`. -/
theorem add (ha : a.eval ρ = x) (hb : b.eval ρ = y) : (Expr.add a b).eval ρ = x + y := by
  rw [Expr.eval, ha, hb]

/-- A difference: if `a` denotes `x` and `b` denotes `y`, then `Expr.sub a b` denotes `x - y`. -/
theorem sub (ha : a.eval ρ = x) (hb : b.eval ρ = y) : (Expr.sub a b).eval ρ = x - y := by
  rw [Expr.eval, ha, hb]

/-- A product: if `a` denotes `x` and `b` denotes `y`, then `Expr.mul a b` denotes `x * y`. -/
theorem mul (ha : a.eval ρ = x) (hb : b.eval ρ = y) : (Expr.mul a b).eval ρ = x * y := by
  rw [Expr.eval, ha, hb]

/-- A quotient: if `a` denotes `x` and `b` denotes `y`, then `Expr.div a b` denotes `x / y`. -/
theorem div (ha : a.eval ρ = x) (hb : b.eval ρ = y) : (Expr.div a b).eval ρ = x / y := by
  rw [Expr.eval, ha, hb]

/-- An opposite: if `a` denotes `x`, then `Expr.neg a` denotes `-x`. -/
theorem neg (ha : a.eval ρ = x) : (Expr.neg a).eval ρ = -x := by rw [Expr.eval, ha]

/-- A reciprocal, as the quotient `1 / a`: if `a` denotes `x`, then `Expr.div (.nat 1) a`
denotes `x⁻¹`. -/
theorem inv (ha : a.eval ρ = x) : (Expr.div (.nat 1) a).eval ρ = x⁻¹ := by
  simp [Expr.eval, ha]

/-- A natural power: if `a` denotes `x`, then `Expr.pow a n` denotes `x ^ n`. -/
theorem pow (ha : a.eval ρ = x) (n : ℕ) : (Expr.pow a n).eval ρ = x ^ n := by rw [Expr.eval, ha]

/-- A square root: if `a` denotes `x`, then `Expr.sqrt a` denotes `Real.sqrt x`. -/
theorem sqrt (ha : a.eval ρ = x) : (Expr.sqrt a).eval ρ = Real.sqrt x := by rw [Expr.eval, ha]

/-- An absolute value: if `a` denotes `x`, then `absE a` denotes `|x|`. -/
theorem abs (ha : a.eval ρ = x) : (absE a).eval ρ = |x| := by rw [eval_absE, ha]

/-- A maximum: if `a` denotes `x` and `b` denotes `y`, then `maxE a b` denotes `max x y`. -/
theorem max (ha : a.eval ρ = x) (hb : b.eval ρ = y) : (maxE a b).eval ρ = Max.max x y := by
  rw [eval_maxE, ha, hb]

/-- A minimum: if `a` denotes `x` and `b` denotes `y`, then `minE a b` denotes `min x y`. -/
theorem min (ha : a.eval ρ = x) (hb : b.eval ρ = y) : (minE a b).eval ρ = Min.min x y := by
  rw [eval_minE, ha, hb]

/-- An exponential: if `a` denotes `x`, then `Expr.exp a` denotes `Real.exp x`. -/
theorem exp (ha : a.eval ρ = x) : (Expr.exp a).eval ρ = Real.exp x := by rw [Expr.eval, ha]

/-- A logarithm: if `a` denotes `x`, then `Expr.log a` denotes `Real.log x`. -/
theorem log (ha : a.eval ρ = x) : (Expr.log a).eval ρ = Real.log x := by rw [Expr.eval, ha]

/-- An arctangent: if `a` denotes `x`, then `Expr.atan a` denotes `Real.arctan x`. -/
theorem arctan (ha : a.eval ρ = x) : (Expr.atan a).eval ρ = Real.arctan x := by
  rw [Expr.eval, ha]

/-- A sine: if `a` denotes `x`, then `Expr.sin a` denotes `Real.sin x`. -/
theorem sin (ha : a.eval ρ = x) : (Expr.sin a).eval ρ = Real.sin x := by rw [Expr.eval, ha]

/-- A cosine: if `a` denotes `x`, then `Expr.cos a` denotes `Real.cos x`. -/
theorem cos (ha : a.eval ρ = x) : (Expr.cos a).eval ρ = Real.cos x := by rw [Expr.eval, ha]

/-- An arcsine: if `a` denotes `x`, then `Expr.asin a` denotes `Real.arcsin x`. -/
theorem arcsin (ha : a.eval ρ = x) : (Expr.asin a).eval ρ = Real.arcsin x := by
  rw [Expr.eval, ha]

/-- An arccosine: if `a` denotes `x`, then `Expr.acos a` denotes `Real.arccos x`. -/
theorem arccos (ha : a.eval ρ = x) : (Expr.acos a).eval ρ = Real.arccos x := by
  rw [Expr.eval, ha]

/-- The cast of a natural number: `Expr.nat n` denotes `(n : ℝ)`. -/
theorem natCast (n : ℕ) : (Expr.nat n : Expr ι).eval ρ = (n : ℝ) := rfl

/-- The cast of an integer: `Expr.int z` denotes `(z : ℝ)`. -/
theorem intCast (z : ℤ) : (Expr.int z : Expr ι).eval ρ = (z : ℝ) := rfl

/-- A numeral that is at least two: `Expr.nat n` denotes the real numeral `n`. -/
theorem ofNat (n : ℕ) [n.AtLeastTwo] : (Expr.nat n : Expr ι).eval ρ = (OfNat.ofNat n : ℝ) := rfl

/-- The numeral `0`: `Expr.nat 0` denotes `(0 : ℝ)`. -/
theorem zero : (Expr.nat 0 : Expr ι).eval ρ = (0 : ℝ) := Nat.cast_zero

/-- The numeral `1`: `Expr.nat 1` denotes `(1 : ℝ)`. -/
theorem one : (Expr.nat 1 : Expr ι).eval ρ = (1 : ℝ) := Nat.cast_one

/-- The number `π`: `Expr.pi` denotes `Real.pi`. -/
theorem pi : (Expr.pi : Expr ι).eval ρ = Real.pi := rfl

/-- A quotient of an integer by a natural number: `Expr.rat num den` denotes
`(num : ℝ) / (den : ℝ)`. -/
theorem rat (num : ℤ) (den : ℕ) : (Expr.rat num den : Expr ι).eval ρ = (num : ℝ) / (den : ℝ) :=
  rfl

/-! Each lemma below says that a condition which holds proves the statement it was read from,
given what its expressions and its parts denote. -/

section Conditions

variable {κ : Type*} {η : κ → ℝ} {σ : ℕ → ℝ} {u v : Expr (κ ⊕ ℕ)} {r s : ℝ}

/-- An inequality `≤`: if `u` denotes `r`, `v` denotes `s` and `Cond.le u v` holds, then
`r ≤ s`. -/
theorem condLe (hu : u.eval (Sum.elim η σ) = r) (hv : v.eval (Sum.elim η σ) = s)
    (h : (Cond.le u v).holds η σ) : r ≤ s := by
  rw [← hu, ← hv]
  exact h

/-- A strict inequality: if `u` denotes `r`, `v` denotes `s` and `Cond.lt u v` holds, then
`r < s`. -/
theorem condLt (hu : u.eval (Sum.elim η σ) = r) (hv : v.eval (Sum.elim η σ) = s)
    (h : (Cond.lt u v).holds η σ) : r < s := by
  rw [← hu, ← hv]
  exact h

/-- An equality: if `u` denotes `r`, `v` denotes `s` and `Cond.eq u v` holds, then `r = s`. -/
theorem condEq (hu : u.eval (Sum.elim η σ) = r) (hv : v.eval (Sum.elim η σ) = s)
    (h : (Cond.eq u v).holds η σ) : r = s := by
  rw [← hu, ← hv]
  exact h

/-- A conjunction: if `c` proves `p` and `d` proves `q` when they hold, and `Cond.and c d`
holds, then `p ∧ q`. -/
theorem condAnd {c d : Cond κ} {p q : Prop} (hc : c.holds η σ → p) (hd : d.holds η σ → q)
    (h : (Cond.and c d).holds η σ) : p ∧ q :=
  ⟨hc h.1, hd h.2⟩

/-- A disjunction: if `c` proves `p` and `d` proves `q` when they hold, and `Cond.or c d`
holds, then `p ∨ q`. -/
theorem condOr {c d : Cond κ} {p q : Prop} (hc : c.holds η σ → p) (hd : d.holds η σ → q)
    (h : (Cond.or c d).holds η σ) : p ∨ q :=
  Or.imp hc hd h

/-- A statement for every real number between two bounds: if `u` denotes `lo`, `v` denotes `hi`,
the condition `c` with the new cell variable `t` proves `p t` when it holds, and
`Cond.onIcc u v depth c` holds, then `p t` for every real `t` with `lo ≤ t` and `t ≤ hi`. -/
theorem condIcc {depth : ℕ} {c : Cond κ} {lo hi : ℝ} {p : ℝ → Prop}
    (hu : u.eval (Sum.elim η σ) = lo) (hv : v.eval (Sum.elim η σ) = hi)
    (hc : ∀ t, c.holds η (push t σ) → p t) (h : (Cond.onIcc u v depth c).holds η σ) :
    ∀ t, lo ≤ t → t ≤ hi → p t := fun t hlo hhi ↦ by
  refine hc t (h t ?_ ?_)
  · rw [hu]; exact hlo
  · rw [hv]; exact hhi

/-- A statement for every real number of a closed interval: `condIcc` with the conclusion
`∀ t ∈ Set.Icc lo hi, p t`. -/
theorem condIccMem {depth : ℕ} {c : Cond κ} {lo hi : ℝ} {p : ℝ → Prop}
    (hu : u.eval (Sum.elim η σ) = lo) (hv : v.eval (Sum.elim η σ) = hi)
    (hc : ∀ t, c.holds η (push t σ) → p t) (h : (Cond.onIcc u v depth c).holds η σ) :
    ∀ t ∈ Set.Icc lo hi, p t :=
  fun t ht ↦ condIcc hu hv hc h t ht.1 ht.2

end Conditions

end Reify

end CAS.Cert

end

public meta section

namespace CAS.Cert

open Lean Meta Elab Tactic Command

/-- `reify ρ cells fuel t` is an expression `a : Expr (Empty ⊕ ℕ)` with a proof of
`a.eval ρ = t`, for a real term `t` built from numerals, casts of natural and integer terms,
`Real.pi`, `+`, `-`, `*`, `/`, `⁻¹`, unary minus, `|·|`, `max`, `min`, `Real.sqrt`, `Real.exp`,
`Real.log`, `Real.arctan`, `Real.sin`, `Real.cos`, `Real.arcsin`, `Real.arccos`, decimal
literals, natural powers and the interval variables `cells`, the innermost first: the one at
position `v` is the cell variable `v` of the environment `ρ`. A term of another form is replaced
by its definition (one definition or one structure projection at a time) and read again. `fuel`
bounds the depth of the term plus the number of such replacements. -/
partial def reify (ρ : Expr) (cells : Array Expr) (fuel : Nat) (t : Expr) :
    TermElabM (Expr × Expr) := do
  if fuel == 0 then throwError "cert_cond: the term is too deep{indentExpr t}"
  let ι := mkApp2 (mkConst ``Sum [Level.zero, Level.zero]) (mkConst ``Empty) (mkConst ``Nat)
  let ctor (c : Name) (args : Array Expr) : Expr := mkAppN (mkApp (mkConst c [Level.zero]) ι) args
  let thm (l : Name) (args : Array Expr) : Expr :=
    mkAppN (mkApp2 (mkConst l [Level.zero]) ι ρ) args
  let unary (c l : Name) (x : Expr) : TermElabM (Expr × Expr) := do
    let (a, ha) ← reify ρ cells (fuel - 1) x
    return (ctor c #[a], thm l #[a, x, ha])
  let derived (f l : Name) (x : Expr) : TermElabM (Expr × Expr) := do
    let (a, ha) ← reify ρ cells (fuel - 1) x
    return (mkApp2 (mkConst f [Level.zero]) ι a, thm l #[a, x, ha])
  let binary (c l : Name) (x y : Expr) : TermElabM (Expr × Expr) := do
    let (a, ha) ← reify ρ cells (fuel - 1) x
    let (b, hb) ← reify ρ cells (fuel - 1) y
    return (ctor c #[a, b], thm l #[a, b, x, y, ha, hb])
  let derived₂ (f l : Name) (x y : Expr) : TermElabM (Expr × Expr) := do
    let (a, ha) ← reify ρ cells (fuel - 1) x
    let (b, hb) ← reify ρ cells (fuel - 1) y
    return (mkApp3 (mkConst f [Level.zero]) ι a b, thm l #[a, b, x, y, ha, hb])
  -- An interval variable is a cell variable; the environment returns it by definition.
  if let some v := cells.findIdx? (· == t) then
    let var := mkApp3 (mkConst ``Sum.inr [Level.zero, Level.zero]) (mkConst ``Empty)
      (mkConst ``Nat) (mkNatLit v)
    return (ctor ``CAS.Verified.Expr.var #[var], mkApp2 (mkConst ``Eq.refl [Level.one])
      (mkConst ``Real) t)
  match_expr t.consumeMData with
  | HAdd.hAdd _ _ _ _ x y => binary ``CAS.Verified.Expr.add ``Reify.add x y
  | HSub.hSub _ _ _ _ x y => binary ``CAS.Verified.Expr.sub ``Reify.sub x y
  | HMul.hMul _ _ _ _ x y => binary ``CAS.Verified.Expr.mul ``Reify.mul x y
  | HDiv.hDiv _ _ _ _ x y => binary ``CAS.Verified.Expr.div ``Reify.div x y
  | Neg.neg _ _ x => unary ``CAS.Verified.Expr.neg ``Reify.neg x
  | Inv.inv _ _ x =>
    let (a, ha) ← reify ρ cells (fuel - 1) x
    return (ctor ``CAS.Verified.Expr.div #[ctor ``CAS.Verified.Expr.nat #[mkNatLit 1], a],
      thm ``Reify.inv #[a, x, ha])
  | abs _ _ _ x => derived ``absE ``Reify.abs x
  | Max.max _ _ x y => derived₂ ``maxE ``Reify.max x y
  | Min.min _ _ x y => derived₂ ``minE ``Reify.min x y
  | Real.sqrt x => unary ``CAS.Verified.Expr.sqrt ``Reify.sqrt x
  | Real.exp x => unary ``CAS.Verified.Expr.exp ``Reify.exp x
  | Real.log x => unary ``CAS.Verified.Expr.log ``Reify.log x
  | Real.arctan x => unary ``CAS.Verified.Expr.atan ``Reify.arctan x
  | Real.sin x => unary ``CAS.Verified.Expr.sin ``Reify.sin x
  | Real.cos x => unary ``CAS.Verified.Expr.cos ``Reify.cos x
  | Real.arcsin x => unary ``CAS.Verified.Expr.asin ``Reify.arcsin x
  | Real.arccos x => unary ``CAS.Verified.Expr.acos ``Reify.arccos x
  | Real.pi => return (ctor ``CAS.Verified.Expr.pi #[], thm ``Reify.pi #[])
  | HPow.hPow _ β _ _ x n =>
    unless β.isConstOf ``Nat do
      throwError "cert_cond: the exponent is not a natural number{indentExpr t}"
    let (a, ha) ← reify ρ cells (fuel - 1) x
    return (ctor ``CAS.Verified.Expr.pow #[a, n], thm ``Reify.pow #[a, x, ha, n])
  | Nat.cast _ _ n => return (ctor ``CAS.Verified.Expr.nat #[n], thm ``Reify.natCast #[n])
  | Int.cast _ _ z => return (ctor ``CAS.Verified.Expr.int #[z], thm ``Reify.intCast #[z])
  | OfNat.ofNat _ n _ =>
    match n.rawNatLit? with
    | some 0 => return (ctor ``CAS.Verified.Expr.nat #[mkNatLit 0], thm ``Reify.zero #[])
    | some 1 => return (ctor ``CAS.Verified.Expr.nat #[mkNatLit 1], thm ``Reify.one #[])
    | some _ =>
      let inst ← synthInstance (mkApp (mkConst ``Nat.AtLeastTwo) n)
      return (ctor ``CAS.Verified.Expr.nat #[n], thm ``Reify.ofNat #[n, inst])
    | none => throwError "cert_cond: unsupported numeral{indentExpr t}"
  | OfScientific.ofScientific _ _ m s e =>
    -- A decimal literal is the quotient of its digits by a power of ten.
    let (some digits, some exponent) := (m.rawNatLit? <|> m.nat?, e.rawNatLit? <|> e.nat?)
      | throwError "cert_cond: unsupported decimal literal{indentExpr t}"
    let (num, den) := if s.isConstOf ``Bool.true then (digits, 10 ^ exponent)
      else (digits * 10 ^ exponent, 1)
    let numE := mkApp (mkConst ``Int.ofNat) (mkNatLit num)
    let denE := mkNatLit den
    let real := mkConst ``Real
    let quotient ← mkAppM ``HDiv.hDiv
      #[← mkAppOptM ``Int.cast #[real, none, numE], ← mkAppOptM ``Nat.cast #[real, none, denE]]
    let equal ← mkFreshExprSyntheticOpaqueMVar (← mkEq quotient t)
    let rest ← Tactic.run equal.mvarId! (evalTactic (← `(tactic| norm_num)))
    unless rest.isEmpty do
      throwError "cert_cond: the decimal literal was not evaluated{indentExpr t}"
    return (ctor ``CAS.Verified.Expr.rat #[numE, denE],
      ← mkEqTrans (thm ``Reify.rat #[numE, denE]) (← instantiateMVars equal))
  | _ =>
    -- Not an arithmetic term: reduce or unfold its head once and read it again.
    let t₁ ← whnfCore t
    let next ← (do
      if t₁ != t then pure (some t₁)
      else if let some f ← reduceProj? t.getAppFn then
        pure (some (mkAppN f t.getAppArgs).headBeta)
      else unfoldDefinition? t)
    match next with
    | some t' =>
      try reify ρ cells (fuel - 1) t'
      catch error => throwError "{error.toMessageData}\nwhile unfolding{indentExpr t}"
    | none => throwError "cert_cond: unsupported term{indentExpr t}"

/-- The environment of the expressions of a statement without data whose interval variables
have the values `σ : ℕ → ℝ`. -/
def reifyEnv (σ : Expr) : MetaM Expr :=
  mkAppOptM ``Sum.elim #[mkConst ``Empty, mkConst ``Nat, mkConst ``Real,
    mkApp (mkConst ``Empty.elim [Level.one]) (mkConst ``Real), σ]

/-- `reifyCond cells σ depth goal` reads the proposition `goal` as a condition: it returns
`c : Cond Empty` and a proof of `c.holds Empty.elim σ → goal`. The statement is a relation
`≤`, `<`, `≥`, `>` or `=` between real terms that `reify` reads, a conjunction, a disjunction,
or `∀ x, lo ≤ x → x ≤ hi → …` or `∀ x ∈ Set.Icc lo hi, …` for a real `x`, which becomes
`Cond.onIcc` with `depth` cuts; `cells` are the interval variables around `goal`, the innermost
first, and `σ` their values. -/
partial def reifyCond (cells : Array Expr) (σ depth goal : Expr) : TermElabM (Expr × Expr) := do
  let goal := (← instantiateMVars goal).consumeMData
  let empty := mkConst ``Empty
  let noData := mkApp (mkConst ``Empty.elim [Level.one]) (mkConst ``Real)
  let ρ ← reifyEnv σ
  let relation (α : Expr) (cond rule : Name) (x y : Expr) : TermElabM (Expr × Expr) := do
    unless (← whnfR α).isConstOf ``Real do
      throwError "cert_cond: not a relation between real numbers{indentExpr goal}"
    let (a, ha) ← reify ρ cells 1000 x
    let (b, hb) ← reify ρ cells 1000 y
    return (mkApp3 (mkConst cond [Level.zero]) empty a b,
      mkAppN (mkConst rule [Level.zero]) #[empty, noData, σ, a, b, x, y, ha, hb])
  let both (cond rule : Name) (p q : Expr) : TermElabM (Expr × Expr) := do
    let (c, hc) ← reifyCond cells σ depth p
    let (d, hd) ← reifyCond cells σ depth q
    return (mkApp3 (mkConst cond [Level.zero]) empty c d,
      mkAppN (mkConst rule [Level.zero]) #[empty, noData, σ, c, d, p, q, hc, hd])
  match_expr goal with
  | LE.le α _ x y => relation α ``Cond.le ``Reify.condLe x y
  | LT.lt α _ x y => relation α ``Cond.lt ``Reify.condLt x y
  | GE.ge α _ x y => relation α ``Cond.le ``Reify.condLe y x
  | GT.gt α _ x y => relation α ``Cond.lt ``Reify.condLt y x
  | Eq α x y => relation α ``Cond.eq ``Reify.condEq x y
  | And p q => both ``Cond.and ``Reify.condAnd p q
  | Or p q => both ``Cond.or ``Reify.condOr p q
  | _ =>
    let .forallE name domain body _ := goal
      | throwError "cert_cond: the statement is not a relation between real numbers, a \
          conjunction, a disjunction or a statement on an interval{indentExpr goal}"
    unless (← whnfR domain).isConstOf ``Real do
      throwError "cert_cond: `{name}` does not range over the real numbers{indentExpr goal}"
    withLocalDeclD name domain fun x ↦ do
      let unsupported : MessageData :=
        m!"cert_cond: `{name}` is not bounded as `lo ≤ {name} → {name} ≤ hi → …` or \
          `{name} ∈ Set.Icc lo hi → …`{indentExpr goal}"
      -- The bounds of `x` and the statement under them.
      let (lo, hi, inner, rule) ← (do
        let .forallE _ first rest _ := body.instantiate1 x | throwError unsupported
        if rest.hasLooseBVars then throwError unsupported
        match_expr first with
        | Membership.mem _ _ _ set y =>
          let_expr Set.Icc _ _ lo hi := set | throwError unsupported
          unless y == x do throwError unsupported
          pure (lo, hi, rest, ``Reify.condIccMem)
        | LE.le _ _ lo y =>
          unless y == x do throwError unsupported
          let .forallE _ second rest _ := rest | throwError unsupported
          if rest.hasLooseBVars then throwError unsupported
          let_expr LE.le _ _ z hi := second | throwError unsupported
          unless z == x do throwError unsupported
          pure (lo, hi, rest, ``Reify.condIcc)
        | _ => throwError unsupported)
      if lo.containsFVar x.fvarId! || hi.containsFVar x.fvarId! then
        throwError "cert_cond: a bound of `{name}` depends on `{name}`{indentExpr goal}"
      let (c, hc) ← reifyCond (#[x] ++ cells) (← mkAppM ``CAS.Cert.push #[x, σ]) depth inner
      if c.containsFVar x.fvarId! then
        throwError "cert_cond: an exponent or a cast depends on `{name}`{indentExpr goal}"
      let (a, ha) ← reify ρ cells 1000 lo
      let (b, hb) ← reify ρ cells 1000 hi
      return (mkApp5 (mkConst ``Cond.onIcc [Level.zero]) empty a b depth c,
        mkAppN (mkConst rule [Level.zero]) #[empty, noData, σ, a, b, depth, c, lo, hi,
          ← mkLambdaFVars #[x] inner, ha, hb, ← mkLambdaFVars #[x] hc])

/-- Proves the statement `statement` by `cert_eval`. Returns its proof, or the error; the state
is restored on failure. -/
def evalChecked (statement : Expr) : TacticM (Except Exception Expr) := do
  let checked ← mkFreshExprSyntheticOpaqueMVar statement
  let saved ← saveState
  try
    let rest ← Tactic.run checked.mvarId! (evalTactic (← `(tactic| cert_eval)))
    unless rest.isEmpty do throwError "the test was not decided"
    return .ok (← instantiateMVars checked)
  catch error =>
    saved.restore
    return .error error

/-- Reads the goal as a condition and evaluates its test at `precision` bits with `depth` cuts
of every interval. Closes the goal and returns `none` when the test passes, and returns the
error of the test otherwise; a goal that is not a condition is an error of its own. -/
def closeByCond (goal : MVarId) (precision depth : Nat) : TacticM (Option Exception) :=
  goal.withContext do
    let target := (← instantiateMVars (← goal.getType)).consumeMData
    let σ := mkConst ``Reify.noCells
    let (c, sound) ← reifyCond #[] σ (mkNatLit depth) target
    let noData := mkApp (mkConst ``Empty.elim [Level.one]) (mkConst ``CAS.Numerics.GridBall)
    let run ← mkEq (mkApp4 (mkConst ``Cond.run [Level.zero]) (mkConst ``Empty)
      (mkNatLit precision) noData c) (mkConst ``Bool.true)
    match ← evalChecked run with
    | .error error => return some error
    | .ok passed =>
      let proof := mkApp sound
        (mkApp4 (mkConst ``CAS.Cert.holds_closed) (mkNatLit precision) c σ passed)
      unless ← isDefEq (← inferType proof) target do
        throwError "cert_cond: the proof does not match the goal"
      goal.assign (← instantiateMVars proof)
      return none

/--
`cert_cond`

proves a goal built from relations `a ≤ b`, `a < b`, `a ≥ b`, `a > b` and `a = b` between real
expressions by `∧`, `∨` and statements on intervals, `∀ x, lo ≤ x → x ≤ hi → …` or
`∀ x ∈ Set.Icc lo hi, …`, nested to any depth, so also on boxes. The expressions are built from
numerals, casts of natural and integer terms, `Real.pi`, `+`, `-`, `*`, `/`, `⁻¹`, unary minus,
`|·|`, `max`, `min`, `Real.sqrt`, `Real.exp`, `Real.log`, `Real.arctan`, `Real.sin`, `Real.cos`,
`Real.arcsin`, `Real.arccos`, decimal literals, natural powers and the interval variables;
definitions and structure projections are unfolded. The goal is written as
a condition of `CAS.Cert.Cond` and its test is evaluated by `cert_eval`: in the kernel, or with
compiled code when `cega.nativeCertificates` is set. An interval on which the test fails is cut
in two, at most `depth` times. `cert_cond p` works at precision `p` (default `128`), and
`cert_cond p depth d` cuts at most `d` times (default `8`).
-/
syntax (name := certCond) "cert_cond" (ppSpace colGt num)? (&" depth " num)? : tactic

elab_rules : tactic | `(tactic| cert_cond $[$p]? $[depth $d]?) => do
  let goal ← getMainGoal
  match ← closeByCond goal ((p.map (·.getNat)).getD 128) ((d.map (·.getNat)).getD 8) with
  | none => replaceMainGoal []
  | some error =>
    throwError "cert_cond: the test failed. The statement may be false, or too tight for this \
      precision and this number of cuts, or a denominator may contain zero.\n\
      {error.toMessageData}"

/--
`cert_scalar`

proves a goal `a ≤ b`, `a < b`, `a ≥ b`, `a > b` or `a = b` between closed real expressions, as
`cert_cond` does, by a comparison of balls. When that fails it compares the exact rational
values of both sides, which decides an equality, or an inequality between equal numbers, of
expressions without square roots, absolute values, `π` and elementary functions.
`cert_scalar p` works at precision `p`; the default is `128`.
-/
syntax (name := certScalar) "cert_scalar" (ppSpace colGt num)? : tactic

elab_rules : tactic | `(tactic| cert_scalar $[$p]?) => do
  let goal ← getMainGoal
  goal.withContext do
    let target := (← instantiateMVars (← goal.getType)).consumeMData
    let (exact, exactSound, x, y) ← match_expr target with
      | LE.le _ _ x y => pure (← `(fun p q : ℚ ↦ decide (p ≤ q)), ``CAS.Cert.le_of_ratTest, x, y)
      | LT.lt _ _ x y => pure (← `(fun p q : ℚ ↦ decide (p < q)), ``CAS.Cert.lt_of_ratTest, x, y)
      | GE.ge _ _ x y => pure (← `(fun p q : ℚ ↦ decide (p ≤ q)), ``CAS.Cert.le_of_ratTest, y, x)
      | GT.gt _ _ x y => pure (← `(fun p q : ℚ ↦ decide (p < q)), ``CAS.Cert.lt_of_ratTest, y, x)
      | Eq _ x y => pure (← `(fun p q : ℚ ↦ decide (p = q)), ``CAS.Cert.eq_of_ratTest, x, y)
      | _ => throwError "cert_scalar: the goal is not `a ≤ b`, `a < b` or `a = b`\
          {indentExpr target}"
    -- First the balls, which decide a relation only when there is a gap between its two sides.
    match ← closeByCond goal ((p.map (·.getNat)).getD 128) 0 with
    | none => replaceMainGoal []
    | some ballError =>
      -- Then the exact rational values, for an equality or a relation without a gap.
      let ρ ← reifyEnv (mkConst ``Reify.noCells)
      let (a, ha) ← reify ρ #[] 1000 x
      let (b, hb) ← reify ρ #[] 1000 y
      let relation ← Term.elabTerm exact none
      let rational ← mkEq (mkApp3 (mkConst ``CAS.Cert.ratTest) relation a b) (mkConst ``Bool.true)
      match ← evalChecked rational with
      | .ok passed =>
        let proof := mkAppN (mkConst exactSound) #[a, b, x, y, ha, hb, passed]
        unless ← isDefEq (← inferType proof) target do
          throwError "cert_scalar: the proof does not match the goal"
        goal.assign (← instantiateMVars proof)
        replaceMainGoal []
      | .error _ =>
        throwError "cert_scalar: the test failed. The relation may be false, or too tight for \
          this precision, or a denominator may contain zero, or it may hold without a gap \
          between numbers that are not rational.\n{ballError.toMessageData}"

/-- `cert_close` closes a goal without binders over a finite type: `cert_scalar` for `a ≤ b`,
`a < b` and `a = b` between closed real expressions, the same test in one of the two directions
for `a ≠ b`, `cert_cond` for conjunctions, disjunctions and statements on intervals, and
`decide` otherwise. `cert_close p` works at precision `p`. -/
syntax (name := certClose) "cert_close" (ppSpace colGt num)? : tactic

macro_rules
  | `(tactic| cert_close $[$p]?) =>
    `(tactic| first
      | cert_scalar $[$p]?
      | exact ne_of_lt (by cert_scalar $[$p]?)
      | exact ne_of_gt (by cert_scalar $[$p]?)
      | cert_cond $[$p]?
      | decide)

/-- `cert_decide` closes a finite combination of relations between real numbers and of
statements on intervals: it tries `cert_close`, and otherwise introduces binders, splits a bound
variable of a type `Fin n` into its values, skips the other binders, splits a conjunction and
tries both sides of a disjunction. `cert_decide p` works at precision `p`; the default is
`128`. -/
syntax (name := certDecide) "cert_decide" (ppSpace colGt num)? : tactic

macro_rules
  | `(tactic| cert_decide $[$p]?) =>
    `(tactic| first
      | cert_close $[$p]?
      | (apply And.intro <;> cert_decide $[$p]?)
      | (apply Or.inl; cert_decide $[$p]?)
      | (apply Or.inr; cert_decide $[$p]?)
      | (intro j; fin_cases j <;> cert_decide $[$p]?)
      | (intro _; cert_decide $[$p]?))

/-- Runs `tac` on the goal `g`. Returns `true` if it closes the goal; otherwise the state is
restored. -/
def closeGoal (g : MVarId) (tac : Syntax) : TermElabM Bool := do
  let saved ← saveState
  try
    let rest ← Tactic.run g (evalTactic tac)
    if rest.isEmpty then
      return true
    saved.restore
    return false
  catch _ =>
    saved.restore
    return false

/-- Is `c` a structure whose fields are treated one by one when a field of this type stays
open? `And` is, and so is every structure that is not declared in Lean's core, in its standard
library, in Mathlib or in Batteries, Aesop, Qq or Plausible. A field `Continuous f` stays one
hypothesis. -/
def splitsFurther (c : Name) : CoreM Bool := do
  let env ← getEnv
  unless isStructure env c do return false
  if c == ``And then return true
  match env.getModuleIdxFor? c with
  | some i =>
    let module := env.header.moduleNames[i.toNat]!
    return !([`Init, `Std, `Lean, `Batteries, `Mathlib, `Aesop, `Qq, `Plausible].any
      (·.isPrefixOf module))
  | none => return true

/-- Applies the constructor of the structure in the goal `g` and tries `tac` on every field. A
field that stays open and is itself a structure (`splitsFurther`) is treated in the same way,
and its fields get the name of the outer field as a prefix. Returns the names of the closed
fields and the open fields with their goals. -/
partial def splitFields (g : MVarId) (tac : Syntax) (pre : Name := .anonymous) :
    TermElabM (Array Name × Array (Name × MVarId)) := do
  -- Only a structure is split: `constructor` on another inductive type would choose a case.
  let target ← whnfR (← instantiateMVars (← g.getType))
  unless target.getAppFn.constName?.any (isStructure (← getEnv)) do
    throwError "cert_fields: the goal is not a structure{indentExpr target}"
  let goals ← g.constructor
  let mut closed : Array Name := #[]
  let mut opened : Array (Name × MVarId) := #[]
  for gi in goals do
    let tag := (← gi.getTag).eraseMacroScopes
    let field := if tag.isAnonymous then pre else pre ++ Name.mkSimple tag.getString!
    if ← closeGoal gi tac then
      closed := closed.push field
    else
      let type ← whnfR (← instantiateMVars (← gi.getType))
      let nested ← match type.getAppFn.constName? with
        | some c => pure ((← splitsFurther c) && (← Meta.isProp type))
        | none => pure false
      if nested then
        let (closed', opened') ← splitFields gi tac field
        closed := closed ++ closed'
        opened := opened ++ opened'
      else
        opened := opened.push (field, gi)
  return (closed, opened)

/-- The report of `cert_fields` and `cert_reduce`: the closed and the open fields. The default
closing tactic `cert_decide` closes a field by computation; a tactic given after `by` may close
it in any way, and the report says which of the two it was. -/
def fieldsReport (custom : Bool) (closed : Array Name) (opened : Array Name) : MessageData :=
  let how := if custom then "the given tactic" else "computation"
  m!"{closed.size} of {closed.size + opened.size} fields closed by {how}: {closed.toList}\n\
    {opened.size} open: {opened.toList}"

/-- The closing tactic of `cert_fields` and `cert_reduce`: the one given after `by`, or
`cert_decide` at the given precision. -/
def closingTactic (p : Option (TSyntax `num)) (tac : Option (TSyntax `tactic)) :
    MacroM (TSyntax `tactic) :=
  match tac with
  | some tac => pure tac
  | none => `(tactic| cert_decide $[$p]?)

/--
`cert_fields`

applies the constructor of the structure in the goal and closes every field that the closing
tactic decides. The other fields stay as goals, named after the fields; the report lists both.
The closing tactic is `cert_decide` at precision `128`; `cert_fields p` sets the precision and
`cert_fields by tac` gives another closing tactic.
-/
syntax (name := certFields) "cert_fields" (ppSpace colGt num)? (" by " tactic)? : tactic

elab_rules : tactic | `(tactic| cert_fields $[$p]? $[by $tac]?) => do
  let closing ← liftMacroM (closingTactic p tac)
  let g ← getMainGoal
  let (closed, opened) ← splitFields g closing
  logInfo (fieldsReport tac.isSome closed (opened.map (·.1)))
  replaceMainGoal (opened.map (·.2)).toList

/--
`cert_reduce name : S`

proves the structure of conditions `S` from the fields that the closing tactic does not decide:
it adds the theorem `name : (open fields) → S`, whose hypotheses are named after the open
fields, and reports the closed and the open fields. The statement `S` must be a closed
proposition whose fields do not depend on each other: it has no universe parameters, which the
command refuses, and the variables of a section are not in scope in it.

* `cert_reduce name at p : S` works at precision `p`; the default is `128`.
* `cert_reduce name : S by tac` uses the closing tactic `tac` in place of `cert_decide`.
* `cert_reduce name (leaving := [f, g]) : S` fails unless the open fields are exactly `f` and
  `g`, in this order. Without it the hypotheses of `name` are whatever the closing tactic
  leaves open, so the statement of `name` changes when a test stops passing, and only the
  report says so: `leaving` is what pins the statement.
* A docstring before the command becomes the docstring of `name`.

The words `leaving` and, in `cert_cond`, `depth` are not reserved: they stay usable as names
and in the options of other tactics, such as `cega (depth := n)`.
-/
syntax (name := certReduce)
  (docComment)? "cert_reduce " ident (" at " num)?
  (atomic(" (" &"leaving") " := " "[" ident,* "]" ")")? " : " term (" by " tactic)? : command

elab_rules : command
  | `(command| $[$doc:docComment]? cert_reduce $id $[at $p]?
      $[(leaving := [$expected,*])]? : $ty $[by $tac]?) => do
  let closing ← liftMacroM (closingTactic p tac)
  let name := (← getCurrNamespace) ++ id.getId
  let (closed, opened) ← liftTermElabM do
    let ty ← Term.elabType ty
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    unless ← Meta.isProp ty do
      throwError "cert_reduce: not a proposition{indentExpr ty}"
    -- The theorem is added without universe parameters.
    if ty.hasLevelParam then
      throwError "cert_reduce: the statement has universe parameters{indentExpr ty}"
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    let (closed, opened) ← splitFields g.mvarId! closing
    if let some expected := expected then
      let want := expected.getElems.map (·.getId)
      unless want == opened.map (·.1) do
        throwError
          "cert_reduce: the open fields are {(opened.map (·.1)).toList} and not {want.toList}"
    let mut decls : Array (Name × Expr) := #[]
    for (field, gi) in opened do
      let t ← instantiateMVars (← gi.getType)
      if t.hasExprMVar then
        throwError "cert_reduce: the field `{field}` depends on another field"
      decls := decls.push (field, t)
    let (type, value) ←
      withLocalDeclsD (decls.map fun (n, t) ↦ (n, fun _ ↦ pure t)) fun xs ↦ do
        for ((_, gi), x) in opened.zip xs do
          gi.assign x
        let v ← instantiateMVars g
        return (← mkForallFVars xs ty, ← mkLambdaFVars xs v)
    let type ← instantiateMVars type
    let value ← instantiateMVars value
    if type.hasMVar || value.hasMVar then
      throwError "cert_reduce: the statement or its proof is not closed"
    addDecl (.thmDecl { name, levelParams := [], type, value })
    Term.addTermInfo' id (mkConst name) (isBinder := true)
    return (closed, opened.map (·.1))
  if let some doc := doc then
    addDocStringCore name (← getDocStringText doc)
  logInfo (m!"{name}: " ++ fieldsReport tac.isSome closed opened)

end CAS.Cert

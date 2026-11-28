/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.GridBallJoin
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Order.Lattice

/-!
# Balls on a binary grid enclosing real numbers

## Motivation

The balls of [GridBall](GridBall.lean) enclose rational numbers. The statements of a numerical
certificate are about real numbers: a table entry, the value of a polynomial at a point of a
cell, `π`, a square root. Which of the theorems on rational balls hold for real numbers, and at
what cost in new proofs?

## The idea

A ball with center `c` and radius `e` at precision `P` is the interval from `(c - e) / 2 ^ P` to
`(c + e) / 2 ^ P`, whose two ends are rational (`GridBall.lo`, `GridBall.hi`). A real number is
enclosed when it lies between them (`EnclosesReal`). Two facts carry every theorem from `ℚ` to
`ℝ` without proving it again.

* A test that compares balls (`leCertain`, `posCertain` and the others) holds at the ends of the
  balls, which are rational, and a real number of a ball lies between its ends.
* The rational numbers of a ball are dense in it, and the statement "the result ball encloses the
  value" describes a closed set of arguments when the operation is continuous. So an operation
  that is sound on the rational numbers of a ball is sound on all its real numbers
  (`EnclosesReal.map`, `EnclosesReal.map₂`).

## Main results

All of them hold for all balls, all precisions and all real numbers.

* `EnclosesReal.map`, `EnclosesReal.map₂`: the transfer of a soundness theorem from `ℚ` to `ℝ`
  for a continuous operation of one and of two arguments.
* `EnclosesReal.add`, `.sub`, `.neg`, `.mul`, `.inv`, `.abs`, `.pow`: the real forms of the
  soundness theorems of `GridBall`, each one line from its rational form.
* `EnclosesReal.le_of_leCertain`, `.lt_of_ltCertain`, `.pos_of_posCertain`: a test on balls
  proves the order between the real numbers they enclose.
* `EnclosesReal.eq_of_sameCertain`: two balls of radius zero with the same center enclose the
  same real number.
* `enclosesReal_hull`: the ball `hull a b`, centered between two balls, encloses every real
  number between a number of `a` and a number of `b`. It is the ball of a cell of a mesh whose
  end points are enclosed by `a` and `b`. `mid a b` is the point at its center, where a cell is
  cut in two.

## Relations

* `enclosesReal_ratCast` says that `EnclosesReal` at a rational number is `GridBall.Encloses`, so
  each real theorem here has its rational form in `CAS.Numerics.GridBall` as the case of a
  rational argument.
* [GridBallRange](GridBallRange.lean) carries the interval functions of SymLean (square root,
  exponential, logarithm, arctangent, sine, cosine, arcsine, arccosine) and `π` to single balls
  with `enclosesReal_hull`.
* `hull` uses `centerDist` of [GridBallJoin](GridBallJoin.lean). `GridBall.join` there also
  contains two balls, around the center of the first and with about twice the radius; `hull` is
  centered between the two, which keeps the ball of a cell small.
* `CAS.Cert.ball_encloses` ([Ball](../Cert/Ball.lean)) is the induction over an expression that
  uses these theorems, one per operation.

## Scope

Only the operations and tests that the evaluator of `CAS.Cert` uses have a real form here. The
minimum and the maximum, the tests `nonnegCertain`, `negCertain` and `nonposCertain` and the
quotient `divPos` follow in one line each from their rational forms, by `EnclosesReal.map`,
`EnclosesReal.map₂` or the ends of a ball, when a user needs them. The products and powers for
nonnegative arguments (`mulNonneg`, `sqNonneg`, `powNonneg`) do not follow from the transfer as
it is stated: their rational forms assume a nonnegative argument, and the transfer asks for the
rational form at every rational number of the ball. The rounding operations `floorGrid` and
`ceilGrid` do not either: a floor is not continuous.
-/

@[expose] public section

namespace CAS.Numerics.GridBall

/-- `s` encloses the real number `x` at precision `P`: if `s` is valid, `x 2 ^ P` lies within
the radius of the center. An invalid ball encloses every real number. -/
def EnclosesReal (P : ℕ) (s : GridBall) (x : ℝ) : Prop :=
  s.ok = true → |x * 2 ^ P - s.center| ≤ s.e

/-- The lower end `(center - e) / 2 ^ P` of a ball, a rational number. -/
def lo (P : ℕ) (s : GridBall) : ℚ := ((s.center : ℚ) - s.e) / 2 ^ P

/-- The upper end `(center + e) / 2 ^ P` of a ball, a rational number. -/
def hi (P : ℕ) (s : GridBall) : ℚ := ((s.center : ℚ) + s.e) / 2 ^ P

/-- A valid ball encloses exactly the real numbers between its two ends. -/
theorem enclosesReal_iff {P : ℕ} {s : GridBall} {x : ℝ} :
    s.EnclosesReal P x ↔ (s.ok = true → (lo P s : ℝ) ≤ x ∧ x ≤ (hi P s : ℝ)) := by
  have h2 : (0 : ℝ) < 2 ^ P := by positivity
  simp only [EnclosesReal, lo, hi, abs_le]
  push_cast
  rw [div_le_iff₀ h2, le_div_iff₀ h2]
  constructor <;> intro h hok <;> have := h hok <;> constructor <;> linarith

/-- At a rational number, `EnclosesReal` is the enclosure of `CAS.Numerics.GridBall`. -/
theorem enclosesReal_ratCast {P : ℕ} {s : GridBall} {q : ℚ} :
    s.EnclosesReal P (q : ℝ) ↔ s.Encloses P q := by
  simp only [EnclosesReal, Encloses]
  constructor <;> intro h hok <;> have := h hok <;> exact_mod_cast this

/-- A ball encloses its lower end. -/
theorem encloses_lo (P : ℕ) (s : GridBall) : s.Encloses P (lo P s) := by
  intro _
  have h2 : (2 : ℚ) ^ P ≠ 0 := by positivity
  rw [lo, div_mul_cancel₀ _ h2, sub_sub_cancel_left, abs_neg, Nat.abs_cast]

/-- A ball encloses its upper end. -/
theorem encloses_hi (P : ℕ) (s : GridBall) : s.Encloses P (hi P s) := by
  intro _
  have h2 : (2 : ℚ) ^ P ≠ 0 := by positivity
  rw [hi, div_mul_cancel₀ _ h2, add_sub_cancel_left, Nat.abs_cast]

/-- Every ball encloses the real number of its center, `center / 2 ^ P`. -/
theorem enclosesReal_center (P : ℕ) (s : GridBall) : s.EnclosesReal P ((s.center : ℝ) / 2 ^ P) := by
  intro _
  have h2 : (2 : ℝ) ^ P ≠ 0 := by positivity
  rw [div_mul_cancel₀ _ h2, sub_self, abs_zero]
  exact Nat.cast_nonneg _

/-- An invalid ball encloses every real number. -/
theorem enclosesReal_of_not_ok {P : ℕ} {s : GridBall} (h : s.ok = false) (x : ℝ) :
    s.EnclosesReal P x := fun hok ↦ by simp [h] at hok

/-- The real numbers of a ball form a closed set. -/
theorem isClosed_enclosesReal (P : ℕ) (s : GridBall) : IsClosed {x : ℝ | s.EnclosesReal P x} := by
  cases hok : s.ok
  · simp [EnclosesReal, hok]
  · have : {x : ℝ | s.EnclosesReal P x} = Set.Icc (lo P s : ℝ) (hi P s) := by
      ext x
      simp [enclosesReal_iff, hok]
    rw [this]
    exact isClosed_Icc

/-! ### Density of the rational numbers of a ball -/

/-- Every real number of a ball is a limit of rational numbers of the ball: the ball is an
interval with rational ends, or the whole line when it is invalid. -/
theorem EnclosesReal.mem_closure {P : ℕ} {s : GridBall} {x : ℝ} (hx : s.EnclosesReal P x) :
    x ∈ closure {y : ℝ | ∃ q : ℚ, s.Encloses P q ∧ (q : ℝ) = y} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  cases hok : s.ok
  · -- An invalid ball encloses every rational number.
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (sub_lt_self x hε)
    refine ⟨q, ⟨q, fun h ↦ by simp [hok] at h, rfl⟩, ?_⟩
    rw [Real.dist_eq, abs_of_pos (by linarith)]
    linarith
  · obtain ⟨hl, hu⟩ := enclosesReal_iff.mp hx hok
    rcases hl.eq_or_lt with heq | hlt
    · -- The lower end is rational.
      exact ⟨x, ⟨lo P s, encloses_lo P s, heq⟩, by simpa using hε⟩
    · -- Otherwise a rational number lies between the lower end and `x`, as close to `x` as asked.
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hlt (sub_lt_self x hε))
      have hq : s.Encloses P q := by
        rw [← enclosesReal_ratCast, enclosesReal_iff]
        exact fun _ ↦ ⟨((le_max_left _ _).trans_lt hq1).le, hq2.le.trans hu⟩
      refine ⟨q, ⟨q, hq, rfl⟩, ?_⟩
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      linarith [(le_max_right (lo P s : ℝ) (x - ε)).trans_lt hq1]

/-! ### Transfer from the rational to the real numbers -/

/-- **Transfer for one argument.** Let `f` be a real function that is continuous on the real
numbers of the ball `a` (needed only when the result ball `r` is valid) and agrees with the
rational function `g` on rational numbers. If `r` encloses `g q` for every rational `q` of `a`,
then `r` encloses `f x` for every real `x` of `a`.

This is how a soundness theorem of `GridBall`, proved on `ℚ`, becomes a theorem on `ℝ`. The set
of `x` in `a` with `f x` in `r` is closed, and it contains the rational numbers of `a`, which
are dense in `a`. -/
theorem EnclosesReal.map {P : ℕ} {a r : GridBall} {f : ℝ → ℝ} {g : ℚ → ℚ}
    (hf : r.ok = true → ContinuousOn f {x | a.EnclosesReal P x})
    (hfg : ∀ q : ℚ, f q = (g q : ℚ))
    (hg : ∀ q : ℚ, a.Encloses P q → r.Encloses P (g q))
    {x : ℝ} (hx : a.EnclosesReal P x) : r.EnclosesReal P (f x) := by
  intro hr
  -- The arguments in `a` whose value lies in `r` form a closed set.
  have hclosed := (hf hr).preimage_isClosed_of_isClosed (isClosed_enclosesReal P a)
    (isClosed_enclosesReal P r)
  -- It contains the rational numbers of `a`.
  have hsub : {y : ℝ | ∃ q : ℚ, a.Encloses P q ∧ (q : ℝ) = y} ⊆
      {x | a.EnclosesReal P x} ∩ f ⁻¹' {y | r.EnclosesReal P y} := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨enclosesReal_ratCast.mpr hq, ?_⟩
    change r.EnclosesReal P (f q)
    rw [hfg]
    exact enclosesReal_ratCast.mpr (hg q hq)
  exact (closure_minimal hsub hclosed hx.mem_closure).2 hr

/-- **Transfer for two arguments.** Let `f` be a real function of two arguments that is
continuous on the pairs of real numbers of the balls `a` and `b` (needed only when the result
ball `r` is valid) and agrees with the rational function `g` on rational numbers. If `r`
encloses `g q q'` for all rational `q` of `a` and `q'` of `b`, then `r` encloses `f x y` for all
real `x` of `a` and `y` of `b`. The proof is that of `EnclosesReal.map` on the product. -/
theorem EnclosesReal.map₂ {P : ℕ} {a b r : GridBall} {f : ℝ → ℝ → ℝ} {g : ℚ → ℚ → ℚ}
    (hf : r.ok = true → ContinuousOn (fun p : ℝ × ℝ ↦ f p.1 p.2)
      ({x | a.EnclosesReal P x} ×ˢ {y | b.EnclosesReal P y}))
    (hfg : ∀ q q' : ℚ, f q q' = (g q q' : ℚ))
    (hg : ∀ q q' : ℚ, a.Encloses P q → b.Encloses P q' → r.Encloses P (g q q'))
    {x y : ℝ} (hx : a.EnclosesReal P x) (hy : b.EnclosesReal P y) :
    r.EnclosesReal P (f x y) := by
  intro hr
  have hclosed := (hf hr).preimage_isClosed_of_isClosed
    ((isClosed_enclosesReal P a).prod (isClosed_enclosesReal P b)) (isClosed_enclosesReal P r)
  have hsub : {y : ℝ | ∃ q : ℚ, a.Encloses P q ∧ (q : ℝ) = y} ×ˢ
      {y : ℝ | ∃ q : ℚ, b.Encloses P q ∧ (q : ℝ) = y} ⊆
      ({x | a.EnclosesReal P x} ×ˢ {y | b.EnclosesReal P y}) ∩
        (fun p : ℝ × ℝ ↦ f p.1 p.2) ⁻¹' {y | r.EnclosesReal P y} := by
    rintro ⟨_, _⟩ ⟨⟨q, hq, rfl⟩, ⟨q', hq', rfl⟩⟩
    refine ⟨⟨enclosesReal_ratCast.mpr hq, enclosesReal_ratCast.mpr hq'⟩, ?_⟩
    change r.EnclosesReal P (f q q')
    rw [hfg]
    exact enclosesReal_ratCast.mpr (hg q q' hq hq')
  have hmem : (x, y) ∈ closure ({y : ℝ | ∃ q : ℚ, a.Encloses P q ∧ (q : ℝ) = y} ×ˢ
      {y : ℝ | ∃ q : ℚ, b.Encloses P q ∧ (q : ℝ) = y}) := by
    rw [closure_prod_eq]
    exact ⟨hx.mem_closure, hy.mem_closure⟩
  exact (closure_minimal hsub hclosed hmem).2 hr

/-! ### Tests -/

/-- A real number of a valid ball lies above the lower end. -/
theorem EnclosesReal.lo_le {P : ℕ} {s : GridBall} {x : ℝ} (hx : s.EnclosesReal P x)
    (hok : s.ok = true) : (lo P s : ℝ) ≤ x := (enclosesReal_iff.mp hx hok).1

/-- A real number of a valid ball lies below the upper end. -/
theorem EnclosesReal.le_hi {P : ℕ} {s : GridBall} {x : ℝ} (hx : s.EnclosesReal P x)
    (hok : s.ok = true) : x ≤ (hi P s : ℝ) := (enclosesReal_iff.mp hx hok).2

/-- If `leCertain a b` holds, `a` encloses the real `x` and `b` encloses the real `y`, then
`x ≤ y`. From `le_of_leCertain` at the upper end of `a` and the lower end of `b`. -/
theorem EnclosesReal.le_of_leCertain {P : ℕ} {a b : GridBall} {x y : ℝ}
    (ha : a.EnclosesReal P x) (hb : b.EnclosesReal P y) (h : leCertain a b = true) : x ≤ y := by
  have hok : a.ok = true ∧ b.ok = true := by
    simp only [leCertain, Bool.and_eq_true] at h
    exact h.1
  have := GridBall.le_of_leCertain (encloses_hi P a) (encloses_lo P b) h
  exact (ha.le_hi hok.1).trans ((Rat.cast_le.mpr this).trans (hb.lo_le hok.2))

/-- If `ltCertain a b` holds, `a` encloses the real `x` and `b` encloses the real `y`, then
`x < y`. From `lt_of_ltCertain` at the upper end of `a` and the lower end of `b`. -/
theorem EnclosesReal.lt_of_ltCertain {P : ℕ} {a b : GridBall} {x y : ℝ}
    (ha : a.EnclosesReal P x) (hb : b.EnclosesReal P y) (h : ltCertain a b = true) : x < y := by
  have hok : a.ok = true ∧ b.ok = true := by
    simp only [ltCertain, Bool.and_eq_true] at h
    exact h.1
  have := GridBall.lt_of_ltCertain (encloses_hi P a) (encloses_lo P b) h
  exact (ha.le_hi hok.1).trans_lt ((Rat.cast_lt.mpr this).trans_le (hb.lo_le hok.2))

/-- If `posCertain a` holds and `a` encloses the real `x`, then `0 < x`. -/
theorem EnclosesReal.pos_of_posCertain {P : ℕ} {a : GridBall} {x : ℝ}
    (ha : a.EnclosesReal P x) (h : posCertain a = true) : 0 < x := by
  have hok : a.ok = true := by
    simp only [posCertain, Bool.and_eq_true] at h
    exact h.1
  have := GridBall.pos_of_posCertain (encloses_lo P a) h
  exact (Rat.cast_pos.mpr this).trans_le (ha.lo_le hok)

/-- Both balls are valid, have radius zero and the same center: they enclose one number. -/
def sameCertain (a b : GridBall) : Bool :=
  a.ok && b.ok && Nat.beq a.e 0 && Nat.beq b.e 0 &&
    Nat.beq (Nat.add a.p b.n) (Nat.add b.p a.n)

/-- If `sameCertain a b` holds, `a` encloses the real `x` and `b` encloses the real `y`, then
`x = y`: a ball of radius zero encloses its center only. -/
theorem EnclosesReal.eq_of_sameCertain {P : ℕ} {a b : GridBall} {x y : ℝ}
    (ha : a.EnclosesReal P x) (hb : b.EnclosesReal P y) (h : sameCertain a b = true) : x = y := by
  simp only [sameCertain, Bool.and_eq_true, Nat.beq_eq, Nat.add_eq] at h
  obtain ⟨⟨⟨⟨hoa, hob⟩, hea⟩, heb⟩, hc⟩ := h
  have h2 : (0 : ℝ) < 2 ^ P := by positivity
  have h1 := ha hoa
  have h3 := hb hob
  rw [hea, Nat.cast_zero, abs_nonpos_iff, sub_eq_zero] at h1
  rw [heb, Nat.cast_zero, abs_nonpos_iff, sub_eq_zero] at h3
  have hcc : (a.center : ℝ) = b.center := by
    have : a.center = b.center := by simp only [center]; omega
    rw [this]
  exact mul_right_cancel₀ h2.ne' (h1.trans (hcc.trans h3.symm))

/-! ### Constants -/

/-- `ofNat P c` encloses the real number `c`. -/
theorem enclosesReal_ofNat (P c : ℕ) : (ofNat P c).EnclosesReal P c := by
  have := enclosesReal_ratCast.mpr (ofNat_encloses P c)
  simpa using this

/-- The ball `ofFrac P (z < 0) |z| d` encloses the real number `z / d`, also for `d = 0`, where
the ball is invalid. -/
theorem enclosesReal_ofFrac (P : ℕ) (z : ℤ) (d : ℕ) :
    (ofFrac P (decide (z < 0)) z.natAbs d).EnclosesReal P ((z : ℝ) / d) := by
  have := enclosesReal_ratCast.mpr (ofFrac_encloses_signedFrac P (decide (z < 0)) z.natAbs d)
  rw [signedFrac_natAbs] at this
  simpa using this

/-! ### Operations -/

/-- If `a` encloses the real `x` and `b` the real `y`, then `add a b` encloses `x + y`. -/
theorem EnclosesReal.add {P : ℕ} {a b : GridBall} {x y : ℝ} (ha : a.EnclosesReal P x)
    (hb : b.EnclosesReal P y) : (GridBall.add a b).EnclosesReal P (x + y) :=
  ha.map₂ (fun _ ↦ continuous_add.continuousOn) (fun q q' ↦ (Rat.cast_add q q').symm)
    (fun _ _ hq hq' ↦ add_encloses hq hq') hb

/-- If `a` encloses the real `x` and `b` the real `y`, then `sub a b` encloses `x - y`. -/
theorem EnclosesReal.sub {P : ℕ} {a b : GridBall} {x y : ℝ} (ha : a.EnclosesReal P x)
    (hb : b.EnclosesReal P y) : (GridBall.sub a b).EnclosesReal P (x - y) :=
  ha.map₂ (fun _ ↦ continuous_sub.continuousOn) (fun q q' ↦ (Rat.cast_sub q q').symm)
    (fun _ _ hq hq' ↦ sub_encloses hq hq') hb

/-- If `a` encloses the real `x`, then `neg a` encloses `-x`. -/
theorem EnclosesReal.neg {P : ℕ} {a : GridBall} {x : ℝ} (ha : a.EnclosesReal P x) :
    (GridBall.neg a).EnclosesReal P (-x) :=
  ha.map (fun _ ↦ continuous_neg.continuousOn) (fun q ↦ (Rat.cast_neg q).symm)
    (fun _ hq ↦ neg_encloses hq)

/-- If `a` encloses the real `x` and `b` the real `y`, then `mul P a b` encloses `x * y`. -/
theorem EnclosesReal.mul {P : ℕ} {a b : GridBall} {x y : ℝ} (ha : a.EnclosesReal P x)
    (hb : b.EnclosesReal P y) : (GridBall.mul P a b).EnclosesReal P (x * y) :=
  ha.map₂ (fun _ ↦ continuous_mul.continuousOn) (fun q q' ↦ (Rat.cast_mul q q').symm)
    (fun _ _ hq hq' ↦ mul_encloses hq hq') hb

/-- If `a` encloses the real `x`, then `inv P a` encloses `x⁻¹`. The ball `inv P a` is valid only
when `a` decides that `x` is positive, where the reciprocal is continuous. -/
theorem EnclosesReal.inv {P : ℕ} {a : GridBall} {x : ℝ} (ha : a.EnclosesReal P x) :
    (GridBall.inv P a).EnclosesReal P x⁻¹ :=
  ha.map (fun hr ↦ continuousOn_inv₀.mono fun _ hy ↦
      (EnclosesReal.pos_of_posCertain hy hr).ne')
    (fun q ↦ (Rat.cast_inv q).symm) (fun _ hq ↦ inv_encloses hq)

/-- If `a` encloses the real `x`, then `abs a` encloses `|x|`. -/
theorem EnclosesReal.abs {P : ℕ} {a : GridBall} {x : ℝ} (ha : a.EnclosesReal P x) :
    (GridBall.abs a).EnclosesReal P |x| :=
  ha.map (fun _ ↦ continuous_abs.continuousOn) (fun q ↦ (Rat.cast_abs q).symm)
    (fun _ hq ↦ abs_encloses hq)

/-- If `a` encloses the real `x`, then `pow P a k` encloses `x ^ k`. -/
theorem EnclosesReal.pow {P : ℕ} {a : GridBall} {x : ℝ} (ha : a.EnclosesReal P x) (k : ℕ) :
    (GridBall.pow P a k).EnclosesReal P (x ^ k) :=
  ha.map (fun _ ↦ (continuous_pow k).continuousOn) (fun q ↦ (Rat.cast_pow q k).symm)
    (fun _ hq ↦ pow_encloses hq k)

/-! ### The ball of a cell -/

/-- The ball centered between `a` and `b` that contains both: its center is the mean of the two
centers, with both parts rounded down, and its radius is half their distance `centerDist a b`,
rounded up, plus one grid unit for the rounding of the center, plus the larger of the two
radii. -/
def hull (a b : GridBall) : GridBall :=
  ⟨Nat.div (Nat.add a.p b.p) 2, Nat.div (Nat.add a.n b.n) 2,
    Nat.add (Nat.div (Nat.add (centerDist a b) 3) 2) (Nat.add a.e (Nat.sub b.e a.e)),
    a.ok && b.ok⟩

/-- **The ball of a cell.** If `a` encloses the real `x`, `b` encloses the real `y` and
`x ≤ z ≤ y`, then `hull a b` encloses `z`. So `hull a b` is a ball for a whole cell of a mesh
whose end points are known through the balls `a` and `b`. The center of the hull is within one
unit of the mean of the two centers, and the radius covers half the distance, that unit and both
radii. -/
theorem enclosesReal_hull {P : ℕ} {a b : GridBall} {x y z : ℝ} (ha : a.EnclosesReal P x)
    (hb : b.EnclosesReal P y) (hxz : x ≤ z) (hzy : z ≤ y) : (hull a b).EnclosesReal P z := by
  intro hok
  simp only [hull, Bool.and_eq_true] at hok
  have h2 : (0 : ℝ) < 2 ^ P := by positivity
  have h1 := abs_le.mp (ha hok.1)
  have h3 := abs_le.mp (hb hok.2)
  have hx' := mul_le_mul_of_nonneg_right hxz h2.le
  have hy' := mul_le_mul_of_nonneg_right hzy h2.le
  -- Integer facts on the rounded center and radius, then cast to the real numbers.
  set d := centerDist a b with hd
  have hc1 : 2 * ((a.p + b.p) / 2) ≤ a.p + b.p := Nat.mul_div_le _ 2
  have hc2 : a.p + b.p ≤ 2 * ((a.p + b.p) / 2) + 1 := by omega
  have hc3 : 2 * ((a.n + b.n) / 2) ≤ a.n + b.n := Nat.mul_div_le _ 2
  have hc4 : a.n + b.n ≤ 2 * ((a.n + b.n) / 2) + 1 := by omega
  have hr : d + 2 ≤ 2 * ((d + 3) / 2) := by omega
  have hd1 : (a.p : ℤ) + b.n - (b.p + a.n) ≤ d := by
    simp only [hd, centerDist, Nat.add_eq, Nat.sub_eq]
    omega
  have hd2 : (b.p : ℤ) + a.n - (a.p + b.n) ≤ d := by
    simp only [hd, centerDist, Nat.add_eq, Nat.sub_eq]
    omega
  have he1 : a.e ≤ a.e + (b.e - a.e) := Nat.le_add_right _ _
  have he2 : b.e ≤ a.e + (b.e - a.e) := by omega
  simp only [hull, center, Nat.add_eq, Nat.sub_eq, natDiv_eq_div, ← hd]
  simp only [center] at h1 h3
  -- The rounded quotients and the truncated difference become plain numbers.
  generalize (a.p + b.p) / 2 = cp at hc1 hc2 ⊢
  generalize (a.n + b.n) / 2 = cn at hc3 hc4 ⊢
  generalize (d + 3) / 2 = r at hr ⊢
  generalize b.e - a.e = t at he1 he2 ⊢
  have hc1' := (Nat.cast_le (α := ℝ)).mpr hc1
  have hc2' := (Nat.cast_le (α := ℝ)).mpr hc2
  have hc3' := (Nat.cast_le (α := ℝ)).mpr hc3
  have hc4' := (Nat.cast_le (α := ℝ)).mpr hc4
  have hr' := (Nat.cast_le (α := ℝ)).mpr hr
  have hd1' := (Int.cast_le (R := ℝ)).mpr hd1
  have hd2' := (Int.cast_le (R := ℝ)).mpr hd2
  have he1' := (Nat.cast_le (α := ℝ)).mpr he1
  have he2' := (Nat.cast_le (α := ℝ)).mpr he2
  push_cast at h1 h3 hc1' hc2' hc3' hc4' hr' hd1' hd2' he1' he2' ⊢
  rw [abs_le]
  constructor <;> linarith

/-- The point at the center of `hull a b`, a ball of radius zero: the mean of the centers of
`a` and `b`, with both parts rounded down. A cell is cut in two there. -/
def mid (a b : GridBall) : GridBall :=
  ⟨Nat.div (Nat.add a.p b.p) 2, Nat.div (Nat.add a.n b.n) 2, 0, a.ok && b.ok⟩

end CAS.Numerics.GridBall

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS
public import CAS.Numerics.Tactic
public meta import CAS.CEGA

/-!
# `cega` with IEEE floats

## Motivation

Can `cega` compute its enclosures with IEEE floats of a chosen format instead of exact rationals,
for one call, for a section or for a whole build, and what does each arithmetic prove on the same
goal?

## The idea

A goal of `cega` is about real numbers, and the arithmetic is only how the bound is computed.
FloatLib computes every enclosure. By default the two ends of its intervals are rational numbers.
With `[use_floats]` they are numbers of an IEEE binary format: each operation is enclosed with
exact rationals and the enclosure rounded outward to finite numbers of the format
(`ExecFloat.Binary.intervalRounding`), and the kernel evaluates all of it. The theorem is the
same in both cases, and so are its axioms. What differs is which bounds are in reach. A float end
is a little further out than the rational one, so a bound that holds with less room than the
format's rounding fails, and a wider format proves it. A product past the largest finite number
of the format has no finite upper end, so the call fails with an overflow, where the rationals
have none. And in a float format `cega` has FloatLib's natural interval evaluation only: first
FloatLib's check of the stated bound, which cuts the box where the bound is nearly attained, then
the float query on a uniform subdivision. A sharp bound that the exact planner gets from
monotonicity needs some room. Each of these cases is below with the message that the call prints.

## Main results

Each item is one example or a short list of examples; the general statements are the theorems of
`CAS.CEGA.Refute` and `CAS.CEGA.FloatQuery` that the last section applies.

* `exp_le`, `two_sided`, `inv_le`, `sqrt_two_le`, `exp_one_le`, `pi_le`, `exp_mul_le`,
  `product_bound`, `cos_ge`, `several`, `log_le`, `atan_le`, `rpow_le` (thirteen examples, each
  as `.exact`, `.binary64` and `.binary128`): the same goal proved in exact arithmetic, in
  binary64 and in binary128, with the three standard axioms each time.
* `sqrt_two_digits` (one example): thirty digits of `√2`, out of reach in binary64 and proved in
  binary128.
* `absorbed` (one example): `(1 + x * 1e-20) - 1 ≤ 2e-20`, where binary64 loses the small term
  and binary128 keeps it.
* `pow_overflow` (one example): `10 ^ 200 * 10 ^ 200` overflows in binary64, which the call
  reports, and is proved in binary128 and in exact arithmetic.
* `mul_one_sub_le`, `sin_le`, `two_parabolas_le` (three examples): box goals proved in binary64
  by FloatLib's check, which subdivides the box where it needs to.
* `by_refutation`, `by_hand`, `by_hand_two_sided` (three examples): `boundOn_of_refutes` on
  FloatLib's check, and `boundOn_of_check` and `enclosedOn_of_check` on the float query, applied
  directly, as the tactic applies them.

## Relations

A `cega` call here that proves a bound on a box first tries FloatLib's check of the stated bound:
it ends in `CAS.CEGA.holds_of_refutes`, applied to a refutation of the negation of the bound with
the ends `Check.Endpoints.binary` of the format, or `Check.Endpoints.exact` in exact arithmetic.
When that check falls short, the call ends in `boundOn_of_check`, `enclosedOn_of_check` or one of
the other check theorems of `CAS.CEGA.Query`, applied to `CAS.CEGA.encloseBoxFloat?` in a format
and to the planner's query in exact arithmetic. The last section applies these theorems,
`encloseBoxFloat?_isSome_iff`, `ends_of_encloseBoxFloat?` and `floatObstruction?` to one goal
each. The goals of the first section are those of `CAS.Examples.CEGA.BoxInequalities`,
`ClosedInequalities` and `BareGoals`, which prove them in exact arithmetic only.
`CAS.Examples.CEGA.Refute` applies FloatLib's check in exact arithmetic, and `tests/floats` builds
a small package with exact arithmetic and with binary64 for every call.

## Scope

The sharp bound `x * (1 - x) ≤ 1 / 4` on `[0, 1]` and the exact range of `x / (1 + x)` need the
monotonicity and centered forms of the exact planner, which a float format does not have; the
examples below prove them with some room. Bounds on integrals are computed with exact rationals
and are not run in float arithmetic. A float evaluation costs the kernel more than an exact one,
because each operation rounds its exact result outward with FloatLib's model of the format
(`tests/floats/measure.tsv` has sample kernel times), so a float query on many pieces is slow.
-/

@[expose] public section

namespace CAS.Examples.CEGA.Floats

open CAS.Certificate
open CAS.CEGA
open CAS.Continuum
open CAS.Verified
open FloatLib.Floats.Formats.BinaryInterchange

-- These tests are about the kernel profile, also when the library is built with native checking.
set_option cega.nativeCertificates false
set_option linter.hashCommand false

/-! ## One goal, three arithmetics -/

-- The whitespace linter reads `$exact $sig` in the quotation as an extra space.
set_option linter.style.whitespace false in
open Lean in
/-- `in_each_arithmetic name sig` states the theorem `sig` three times, as `name.exact`,
`name.binary64` and `name.binary128`, each proved by bare `cega` in that arithmetic, and prints
the axioms of the three theorems. Under `set_option trace.cega.refute true in`, the trace names
the arithmetic of FloatLib's check of each theorem, and under `trace.cega.stated` that of the
box query that runs when the check falls short. -/
local macro doc:docComment "in_each_arithmetic " name:ident sig:declSig : command => do
  let exact := mkIdentFrom name (name.getId ++ `exact)
  let double := mkIdentFrom name (name.getId ++ `binary64)
  let quad := mkIdentFrom name (name.getId ++ `binary128)
  `($doc:docComment theorem $exact $sig:declSig := by cega [use_floats := false]
    $doc:docComment theorem $double $sig:declSig := by cega [use_floats := true]
    $doc:docComment theorem $quad $sig:declSig := by cega (arith := binary128)
    #print axioms $exact
    #print axioms $double
    #print axioms $quad)

/--
info: 'CAS.Examples.CEGA.Floats.exp_le.binary128' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.exp_le.binary64' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.exp_le.exact' depends on axioms: [propext, Classical.choice, Quot.sound]
---
trace: [cega.refute] FloatLib check in binary128, stated bound ≤ 68/25: refuted on 1 box, checked by the kernel
---
trace: [cega.refute] FloatLib check in binary64, stated bound ≤ 68/25: refuted on 1 box, checked by the kernel
---
trace: [cega.refute] FloatLib check, stated bound ≤ 68/25: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- The exponential on `[0, 1]`. -/
in_each_arithmetic exp_le (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.72

/--
info: 'CAS.Examples.CEGA.Floats.two_sided.binary128' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.two_sided.binary64' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.two_sided.exact' depends on axioms: [propext, Classical.choice, Quot.sound]
---
trace: [cega.refute] FloatLib check in binary128, stated bounds > 0, < 2: refuted on 3 boxes, checked by the kernel
---
trace: [cega.refute] FloatLib check in binary64, stated bounds > 0, < 2: refuted on 3 boxes, checked by the kernel
---
trace: [cega.refute] FloatLib check, stated bounds > 0, < 2: refuted on 3 boxes, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- A strict two-sided bound, whose two sides FloatLib's check refutes separately: the lower
side on the whole interval, and the upper side on each half, since on the whole interval the
natural evaluation of `x * (1 - x) + 1` gives `[1, 2]`, which does not prove `< 2`. -/
in_each_arithmetic two_sided (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 < x * (1 - x) + 1 ∧ x * (1 - x) + 1 < 2

/--
info: 'CAS.Examples.CEGA.Floats.inv_le.binary128' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.inv_le.binary64' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.inv_le.exact' depends on axioms: [propext, Classical.choice, Quot.sound]
---
trace: [cega.refute] FloatLib check in binary128, stated bound ≤ 2: refuted on 1 box, checked by the kernel
---
trace: [cega.refute] FloatLib check in binary64, stated bound ≤ 2: refuted on 1 box, checked by the kernel
---
trace: [cega.refute] FloatLib check, stated bound ≤ 2: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- A quotient whose divisor stays away from zero. -/
in_each_arithmetic inv_le (x : ℝ) (hx : |x| ≤ 1 / 2) : 1 / (1 - x) ≤ 2

/--
info: 'CAS.Examples.CEGA.Floats.sqrt_two_le.binary128' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.sqrt_two_le.binary64' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.sqrt_two_le.exact' depends on axioms: [propext, Classical.choice, Quot.sound]
---
trace: [cega.refute] FloatLib check in binary128, stated bound ≤ 283/200: refuted on 1 box, checked by the kernel
---
trace: [cega.refute] FloatLib check in binary64, stated bound ≤ 283/200: refuted on 1 box, checked by the kernel
---
trace: [cega.refute] FloatLib check, stated bound ≤ 283/200: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- A closed goal. In a float format FloatLib encloses the square root on a grid finer than the
format and rounds the enclosure outward into it. -/
in_each_arithmetic sqrt_two_le : Real.sqrt 2 ≤ 1.415

/--
info: 'CAS.Examples.CEGA.Floats.exp_one_le.binary128' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.exp_one_le.binary64' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.exp_one_le.exact' depends on axioms: [propext, Classical.choice, Quot.sound]
---
trace: [cega.refute] FloatLib check in binary128, stated bound ≤ 68/25: refuted on 1 box, checked by the kernel
---
trace: [cega.refute] FloatLib check in binary64, stated bound ≤ 68/25: refuted on 1 box, checked by the kernel
---
trace: [cega.refute] FloatLib check, stated bound ≤ 68/25: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- A closed goal with the exponential. -/
in_each_arithmetic exp_one_le : Real.exp 1 ≤ 2.72

/--
info: 'CAS.Examples.CEGA.Floats.pi_le.binary128' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.pi_le.binary64' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.pi_le.exact' depends on axioms: [propext, Classical.choice, Quot.sound]
---
trace: [cega.refute] FloatLib check in binary128, stated bound ≤ 3927/1250: refuted on 1 box, checked by the kernel
---
trace: [cega.refute] FloatLib check in binary64, stated bound ≤ 3927/1250: refuted on 1 box, checked by the kernel
---
trace: [cega.refute] FloatLib check, stated bound ≤ 3927/1250: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- A closed goal with `π`. -/
in_each_arithmetic pi_le : Real.pi ≤ 3.1416

/--
info: 'CAS.Examples.CEGA.Floats.exp_mul_le.binary128' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.exp_mul_le.binary64' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.exp_mul_le.exact' depends on axioms: [propext, Classical.choice, Quot.sound]
---
trace: [cega.refute] FloatLib check in binary128, stated bound ≤ 21: refuted on 1 box, checked by the kernel
---
trace: [cega.refute] FloatLib check in binary64, stated bound ≤ 21: refuted on 1 box, checked by the kernel
---
trace: [cega.refute] FloatLib check, stated bound ≤ 21: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- Two variables. -/
in_each_arithmetic exp_mul_le (x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) (hy : 2 ≤ y) (hy' : y ≤ 3) :
    Real.exp (x * y) ≤ 21

/--
info: 'CAS.Examples.CEGA.Floats.product_bound.binary128' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.product_bound.binary64' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.product_bound.exact' depends on axioms: [propext, Classical.choice, Quot.sound]
---
trace: [cega.refute] FloatLib check in binary128, stated bound ≤ 4: refuted on 1 box, checked by the kernel
---
trace: [cega.refute] FloatLib check in binary64, stated bound ≤ 4: refuted on 1 box, checked by the kernel
---
trace: [cega.refute] FloatLib check, stated bound ≤ 4: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- A certificate goal on a box in `ℝ^2`. -/
in_each_arithmetic product_bound :
    BoundOn (fun p : ℝ^2 ↦ p 0 * p 1) {p : ℝ^2 | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 2 ≤ p 1 ∧ p 1 ≤ 3} 4

/--
info: 'CAS.Examples.CEGA.Floats.cos_ge.binary128' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.cos_ge.binary64' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.cos_ge.exact' depends on axioms: [propext, Classical.choice, Quot.sound]
---
trace: [cega.refute] FloatLib check in binary128, stated bound ≥ 43/50: refuted on 1 box, checked by the kernel
---
trace: [cega.refute] FloatLib check in binary64, stated bound ≥ 43/50: refuted on 1 box, checked by the kernel
---
trace: [cega.refute] FloatLib check, stated bound ≥ 43/50: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- The cosine on a short interval near `100`. -/
in_each_arithmetic cos_ge (x : ℝ) (h0 : 100 ≤ x) (h1 : x ≤ 100001 / 1000) : 0.86 ≤ Real.cos x

/--
info: 'CAS.Examples.CEGA.Floats.several.binary128' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.several.binary64' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.several.exact' depends on axioms: [propext, Classical.choice, Quot.sound]
---
trace: [cega.refute] FloatLib check in binary128, stated bound ≥ 0: refuted on 1 box, checked by the kernel
[cega.refute] FloatLib check in binary128, stated bound ≤ 3: refuted on 1 box, checked by the kernel
[cega.refute] FloatLib check in binary128, stated bound |·| < 1: refuted on 1 box, checked by the kernel
---
trace: [cega.refute] FloatLib check in binary64, stated bound ≥ 0: refuted on 1 box, checked by the kernel
[cega.refute] FloatLib check in binary64, stated bound ≤ 3: refuted on 1 box, checked by the kernel
[cega.refute] FloatLib check in binary64, stated bound |·| < 1: refuted on 1 box, checked by the kernel
---
trace: [cega.refute] FloatLib check, stated bound ≥ 0: refuted on 1 box, checked by the kernel
[cega.refute] FloatLib check, stated bound ≤ 3: refuted on 1 box, checked by the kernel
[cega.refute] FloatLib check, stated bound |·| < 1: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- Three bounds on three expressions, each proved on its own. -/
in_each_arithmetic several (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 ≤ x / (1 + x) ∧ Real.exp x ≤ 3 ∧ |Real.sin x| < 1

/--
info: 'CAS.Examples.CEGA.Floats.log_le.binary128' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.log_le.binary64' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.log_le.exact' depends on axioms: [propext, Classical.choice, Quot.sound]
---
trace: [cega.refute] FloatLib check in binary128, stated bound ≤ 7/10: refuted on 1 box, checked by the kernel
---
trace: [cega.refute] FloatLib check in binary64, stated bound ≤ 7/10: refuted on 1 box, checked by the kernel
---
trace: [cega.refute] FloatLib check, stated bound ≤ 7/10: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- The logarithm on `[1, 2]`. -/
in_each_arithmetic log_le (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ 2) : Real.log x ≤ 0.7

/--
info: 'CAS.Examples.CEGA.Floats.atan_le.binary128' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.atan_le.binary64' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.atan_le.exact' depends on axioms: [propext, Classical.choice, Quot.sound]
---
trace: [cega.refute] FloatLib check in binary128, stated bound ≤ 79/100: refuted on 1 box, checked by the kernel
---
trace: [cega.refute] FloatLib check in binary64, stated bound ≤ 79/100: refuted on 1 box, checked by the kernel
---
trace: [cega.refute] FloatLib check, stated bound ≤ 79/100: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- The arctangent on `[0, 1]`. -/
in_each_arithmetic atan_le (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.arctan x ≤ 0.79

/--
info: 'CAS.Examples.CEGA.Floats.rpow_le.binary128' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.rpow_le.binary64' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'CAS.Examples.CEGA.Floats.rpow_le.exact' depends on axioms: [propext, Classical.choice, Quot.sound]
---
trace: [cega.refute] FloatLib check in binary128, stated bound ≤ 283/100: refuted on 1 box, checked by the kernel
---
trace: [cega.refute] FloatLib check in binary64, stated bound ≤ 283/100: refuted on 1 box, checked by the kernel
---
trace: [cega.refute] FloatLib check, stated bound ≤ 283/100: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- A real power on a positive base. -/
in_each_arithmetic rpow_le (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ 2) : x ^ (1.5 : ℝ) ≤ 2.83

/-! ## Choosing the format

`[use_floats]` is binary64 where no option names another format. `(arith := F)` names any IEEE
binary format of FloatLib, and turns floats on by itself. The trace of each call names the
format that the kernel computed in. -/

/--
trace: [cega.refute] FloatLib check in binary32, stated bound ≤ 273/100: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- binary32, with the flag and the item. -/
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.73 := by
  cega [use_floats := true] (arith := binary32)

/--
trace: [cega.refute] FloatLib check in binary16, stated bound ≤ 273/100: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- binary16, with the item alone. Eleven bits are enough for this bound. -/
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.73 := by
  cega (arith := binary16)

/--
trace: [cega.refute] FloatLib check in FloatFormat.ieee 15 112, stated bound ≤ 273/100: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- A format by its exponent and fraction widths: 15 and 112 bits are binary128. -/
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.73 := by
  cega (arith := FloatFormat.ieee 15 112)

/--
trace: [cega.refute] FloatLib check in binary(p := 113, emax := 16383), stated bound ≤ 273/100: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- A format by its precision and largest exponent, as IEEE 754 names it. -/
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.73 := by
  cega (arith := "binary(p := 113, emax := 16383)")

/-- A format of our own: 20 exponent bits and 100 fraction bits. -/
def wide : FloatFormat := FloatFormat.ieee 20 100

/--
trace: [cega.refute] FloatLib check in wide, stated bound ≤ 273/100: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- Any closed term of type `FloatFormat` that is an IEEE format. -/
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.73 := by
  cega (arith := wide)

/--
trace: [cega.refute] FloatLib check in binary64, stated bound ≤ 11/4: refuted on 1 box, checked by the kernel
---
trace: [cega.refute] FloatLib check in binary64, stated bound ≤ 137/50: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- The flag shares its bracket group with `fast`, in either order. -/
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.74 ∧ Real.exp x ≤ 2.75 :=
  ⟨by cega [fast, use_floats], by cega [use_floats, fast]⟩

/--
trace: [cega.stated] enclose query in binary64, stated bound ∈ [0, 1]: checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- The explicit query in a format, on a certificate goal. -/
example :
    EnclosedOn (fun p : ℝ^1 ↦ p 0 / (1 + p 0)) {p : ℝ^1 | 0 ≤ p 0 ∧ p 0 ≤ 1} 0 1 := by
  cega (arith := binary64) [enclose x in [0, 1]] (x / (1 + x))

/--
trace: [cega.refute] FloatLib check in binary64, stated bound ≤ 69/25: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- A variable named like a format does not change what `[use_floats]` means. -/
example (binary64 : ℝ) (h₀ : 0 ≤ binary64) (h₁ : binary64 ≤ 1) : Real.exp binary64 ≤ 2.76 := by
  cega [use_floats]

/-! ### The option of a section

`set_option cega.arithmetic` sets the arithmetic of every `cega` call after it; a project sets it
for all its modules with `weak.cega.arithmetic` in the Lean options of its lakefile, which Lake
passes to Lean as `-Dweak.cega.arithmetic=binary64`. A call still chooses for itself. -/

section

set_option cega.arithmetic "binary32"

/--
trace: [cega.refute] FloatLib check in binary32, stated bound ≤ 277/100: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- Bare `cega` takes the arithmetic of the section. -/
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.77 := by
  cega

/--
trace: [cega.refute] FloatLib check, stated bound ≤ 139/50: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- `[use_floats := false]` is exact arithmetic for one call. -/
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.78 := by
  cega [use_floats := false]

/--
trace: [cega.refute] FloatLib check in binary32, stated bound ≤ 279/100: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- `[use_floats := true]` keeps the format of the section. -/
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.79 := by
  cega [use_floats := true]

/--
trace: [cega.refute] FloatLib check in binary64, stated bound ≤ 14/5: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- `(arith := F)` chooses another format for one call. -/
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.8 := by
  cega (arith := binary64)

/--
trace: [cega.stated] bound query in binary32, stated bound ≤ 281/100: checked by the kernel
---
trace: [cega.stated] bound query, stated bound ≤ 141/50: checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- The explicit query takes the arithmetic of the section, and `(arith := "exact")` is exact
arithmetic for one query. -/
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.81 ∧ Real.exp x ≤ 2.82 :=
  ⟨by cega [enclose x in [0, 1]] (Real.exp x),
    by cega (arith := "exact") [enclose x in [0, 1]] (Real.exp x)⟩

/--
trace: [cega.refute] FloatLib check, stated bound ≤ 3/4: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- A bound on an integral is computed with exact rationals: in a float section it asks for
them. -/
example : (∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) ≤ 3 / 4 := by
  cega [use_floats := false]

/-- A finite statement has no arithmetic to switch: bare `cega` decides it in the kernel, and the
batch forms are unchanged. -/
example : (∀ i : Fin 6, i.val < 6) ∧ ∀ i : Fin 10, i.val * i.val < 100 :=
  ⟨by cega, by cega [batch := 3]⟩

/--
trace: [cega.refute] FloatLib check, stated bound ≤ 283/100: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- `cas` computes with exact rationals whatever the option is. -/
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.83 := by
  cas

end

/--
info: Try this:
  [apply] cega (arith := binary64)

Lean checked the suggested replacement against the original goal. Selected route: CEGA route: checked box enclosure of an ordinary inequality, arithmetic: binary64 floating point.
-/
#guard_msgs in
/-- `cega?` names the arithmetic of the route that closed the goal, and its suggestion carries the
format, so that it computes in the same arithmetic wherever it is pasted. -/
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.84 := by
  cega? [use_floats]

/--
info: Try this:
  [apply] cega

Lean checked the suggested replacement against the original goal. Selected route: CEGA route: checked box enclosure of an ordinary inequality, arithmetic: exact rationals.
-/
#guard_msgs in
/-- In exact arithmetic the report says so. -/
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.85 := by
  cega?

/--
info: Try this:
  [apply] cega (arith := "exact")

Lean checked the suggested replacement against the original goal. Selected route: CEGA route: checked box enclosure of an ordinary inequality, arithmetic: exact rationals.
-/
#guard_msgs in
set_option cega.arithmetic "binary64" in
/-- An exact call in a float section is suggested with `(arith := "exact")`. -/
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.86 := by
  cega? [use_floats := false]

/--
info: Try this:
  [apply] cega (arith := "exact")

Lean checked the suggested replacement against the original goal. Selected route: CAS route: checked CEGA box enclosure of an ordinary inequality.
-/
#guard_msgs in
set_option cega.arithmetic "binary64" in
/-- `cas?` proves a bound with exact rationals whatever the option is, so in a float section its
suggestion says so too. -/
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.87 := by
  cas?

/--
info: Try this:
  [apply] cega [fast, use_floats]

Lean checked the suggested replacement against the original goal. Selected route: CEGA route: fast profile, arithmetic: binary64 floating point.
-/
#guard_msgs in
/-- `cega? [fast, use_floats]` keeps the call as written and names the format. -/
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 2.88 := by
  cega? [fast, use_floats]

/-! ## A bound that binary64 cannot prove and binary128 can -/

/--
its certified upper bound 6369051672525773/4503599627370496 may be too weak for the stated bound. The goal has no variables, so subdivision does not apply, and the arithmetic is binary64. A wider format, as in `(arith := binary128)`, or exact arithmetic, `cega [use_floats := false]`, may prove it.
-/
#guard_msgs (substring := true) in
/-- Thirty digits of `√2` in binary64: the float above `√2` is `1.41421356237309514…`, past the
stated bound, so the call fails and names the format. -/
example : Real.sqrt 2 ≤ 1.41421356237309504880168872421 := by
  cega [use_floats]

/--
trace: [cega.refute] FloatLib check in binary128, stated bound ≤ 141421356237309504880168872421/100000000000000000000000000000: refuted on 1 box, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- binary128 has 113 bits, about 34 digits, and proves it. -/
theorem sqrt_two_digits : Real.sqrt 2 ≤ 1.41421356237309504880168872421 := by
  cega (arith := binary128)

/-- Exact arithmetic proves it once the square root is asked for at this precision. -/
example : Real.sqrt 2 ≤ 1.41421356237309504880168872421 := by
  cega (prec := 110)

/--
its certified upper bound 1/4503599627370496 may be too weak for the stated bound. The arithmetic is binary64.
-/
#guard_msgs (substring := true) in
/-- A sum that loses its small term: in binary64, `1 + x * 1e-20` rounds up to the float after
`1`, so the difference is enclosed by `2⁻⁵²`, which is far above `2e-20`. This is what
computing in binary64 means, and the message gives the bound that it certified. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : (1 + x * 1e-20) - 1 ≤ 2e-20 := by
  cega [use_floats]

/-- binary128 keeps the small term, and so do the rationals. -/
theorem absorbed (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    (1 + x * 1e-20) - 1 ≤ 2e-20 ∧ (1 + x * 1e-20) - 1 ≤ 3e-20 :=
  ⟨by cega (arith := binary128), by cega⟩

/-! ## Overflow -/

/--
found no certificate: the binary64 evaluation found no enclosure: the enclosure of a product has an end beyond the largest finite binary64 number (overflow). A wider format, as in `(arith := binary128)`, or exact arithmetic, `cega [use_floats := false]`, may prove it.
-/
#guard_msgs (substring := true) in
/-- `10 ^ 200` is a binary64 number and its square is not: the product has no finite upper end,
so FloatLib has no enclosure of it, and the call fails with the format, the operation and the
reason. -/
example : (10 : ℝ) ^ 200 * 10 ^ 200 ≤ 10 ^ 401 := by
  cega [use_floats]

/-- The same goal in binary128, whose largest number is about `1.2e4932`, and in exact
arithmetic, which has no largest number. -/
theorem pow_overflow :
    (10 : ℝ) ^ 200 * 10 ^ 200 ≤ 10 ^ 401 ∧ (10 : ℝ) ^ 200 * 10 ^ 200 ≤ 10 ^ 402 :=
  ⟨by cega (arith := binary128), by cega⟩

/--
found no certificate: the binary32 evaluation found no enclosure: the enclosure of a product has an end beyond the largest finite binary32 number (overflow). A wider format, as in `(arith := binary64)`, or exact arithmetic, `cega [use_floats := false]`, may prove it.
-/
#guard_msgs (substring := true) in
/-- An overflow on a box, in binary32, whose largest number is about `3.4e38`. The message
proposes binary64, the next format of the catalog. -/
example (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ 2) : x * 1e30 * 1e10 ≤ 1e41 := by
  cega (arith := binary32)

/--
the binary32 evaluation found no enclosure: a bound of the box is beyond the largest finite binary32 number (overflow).
-/
#guard_msgs (substring := true) in
/-- A bound of the box that is itself past the largest number of the format. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1e39) : x ≤ 1e39 := by
  cega (arith := binary32)

/-! ## Subdivision in binary64

FloatLib's check, which `cega` tries first, cuts the box itself: it bisects a piece along its
widest coordinate whenever FloatLib's enclosure on that piece does not yet give the stated bound,
so the pieces are small only near the points where the bound is nearly attained. The float query,
which runs when the check falls short, has the uniform subdivision of `(depth := n)` instead: it
cuts the box in two `n` times, each time along the widest coordinate that the expression
mentions, and evaluates the expression on every piece. The calls below keep their depth for that
query. -/

/--
trace: [cega.refute] FloatLib check in binary64, stated bound ≤ 13/50: refuted on 18 boxes, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- FloatLib's check proves `x * (1 - x) ≤ 0.26` on eighteen pieces, the small ones around
`1 / 2`, where the float query would need the sixty-four pieces of depth `6`. -/
theorem mul_one_sub_le (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 0.26 := by
  cega [use_floats] (depth := 6)

/--
trace: [cega.refute] FloatLib check in binary64, stated bound ≤ 17/20: refuted on 6 boxes, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- The sine on `[0, 1]`: the exact planner uses that it increases, and FloatLib's check needs six
pieces, cut toward `1`, where the bound is nearly attained. The float query would need the
thirty-two pieces of depth `5`. -/
theorem sin_le (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.sin x ≤ 0.85 := by
  cega [use_floats] (depth := 5)

/--
trace: [cega.refute] FloatLib check in binary64, stated bound ≤ 13/20: refuted on 28 boxes, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- Two variables: FloatLib's check cuts each piece along its wider coordinate, into twenty-eight
pieces, where the float query would need the sixty-four of depth `6`. -/
theorem two_parabolas_le (x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) (hy : 0 ≤ y) (hy' : y ≤ 1) :
    x * (1 - x) + y * (1 - y) ≤ 0.65 := by
  cega [use_floats] (depth := 6)

/--
trace: [cega.refute] FloatLib check in binary64, stated bound ≤ 2: refuted on 3 boxes, checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- A divisor whose natural enclosure on `[0, 1]` contains zero: FloatLib has no enclosure of the
quotient on the whole box, and its check cuts the box into three pieces, on each of which the
divisor is away from zero. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : 1 / (x ^ 2 - x + 1) ≤ 2 := by
  cega [use_floats]

/--
trace: [cega.stated] subdivided enclose query in binary64, stated bound ∈ [0, 51/100]: checked by the kernel
-/
#guard_msgs (ordering := sorted) in
set_option trace.cega.refute true in
set_option trace.cega.stated true in
/-- The explicit query with a depth, on a certificate goal. -/
example :
    EnclosedOn (fun p : ℝ^1 ↦ p 0 / (1 + p 0)) {p : ℝ^1 | 0 ≤ p 0 ∧ p 0 ≤ 1} 0 0.51 := by
  cega (arith := binary64) (depth := 6) [enclose x in [0, 1]] (x / (1 + x))

/--
info: 'CAS.Examples.CEGA.Floats.mul_one_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mul_one_sub_le

/--
info: 'CAS.Examples.CEGA.Floats.sin_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sin_le

/--
info: 'CAS.Examples.CEGA.Floats.two_parabolas_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms two_parabolas_le

/--
info: 'CAS.Examples.CEGA.Floats.sqrt_two_digits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sqrt_two_digits

/--
info: 'CAS.Examples.CEGA.Floats.absorbed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms absorbed

/--
info: 'CAS.Examples.CEGA.Floats.pow_overflow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pow_overflow

/--
↑33 / ↑128 ≤ 1 / 4
-/
#guard_msgs (substring := true) in
/-- The sharp bound is out of reach of FloatLib's check and of the float query at any depth: a
piece that ends at `1 / 2` is evaluated to a value above `1 / 4`, here `33 / 128` at the depth
that proves `0.26`. Exact arithmetic proves it. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  cega [use_floats] (depth := 6)

/-! ## Other refusals -/

/--
the binary64 evaluation found no enclosure: a divisor interval contains zero in binary64 arithmetic. If the divisor has no zero on the box, `(depth := n)` subdivision may separate it from zero.
-/
#guard_msgs (substring := true) in
/-- A divisor with a zero in the box. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : 1 / (x - 1 / 2) ≤ 2 := by
  cega [use_floats]

/--
the binary64 evaluation found no enclosure: a logarithm has an argument interval that is not positive in binary64 arithmetic. Exact arithmetic, `cega [use_floats := false]`, may prove it.
-/
#guard_msgs (substring := true) in
/-- A logarithm of a negative interval. A wider format does not help, so the message proposes
exact arithmetic only. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.log (x - 2) ≤ 2 := by
  cega [use_floats]

/--
cega integral route: the quadrature of an interval integral computes with exact rationals, so it is not run in binary64 arithmetic. `cega [use_floats := false]` runs it.
-/
#guard_msgs (substring := true) in
/-- A bound on an integral is not computed with floats, and the call says which call computes
it. -/
example : (∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) ≤ 3 / 4 := by
  cega [use_floats]

/--
error: the format `FloatFormat.finite 8 23` is not an IEEE format (`FloatFormat.isIEEE` is false for it). The float arithmetic of `cega` takes IEEE formats only; `FloatFormat.ieee 8 23` has the same widths
-/
#guard_msgs in
/-- A format without infinities is not an IEEE format. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x ≤ 2.72 := by
  cega (arith := FloatFormat.finite 8 23)

/--
error: `decimal64` is not a FloatLib binary format; the arithmetic of `cega` is `"exact"` or a format such as `binary16`, `binary32`, `binary64`, `binary128`, `FloatFormat.ieee e f` for `e` exponent bits and `f` fraction bits, or `"binary(p := 113, emax := 16383)"` for a precision and a largest exponent. A format is a closed term: the variables and hypotheses of the goal are not in its scope.
  Unknown identifier `decimal64`
-/
#guard_msgs in
/-- A name that is not a format. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x ≤ 2.72 := by
  cega (arith := decimal64)

/--
error: `binary(p := 53, emax := 1000)` is not an IEEE binary format: the precision `p` is at least 2, and `emax + 1` is a power of two that is at least 2, as in `binary(p := 53, emax := 1023)` for binary64
-/
#guard_msgs in
/-- A precision and a largest exponent that no IEEE format has. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x ≤ 2.72 := by
  cega (arith := "binary(p := 53, emax := 1000)")

/--
error: `use_floats := false` asks for exact arithmetic and `(arith := binary32)` for a float format; remove one of them
-/
#guard_msgs in
/-- The flag and the item must agree. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x ≤ 2.72 := by
  cega [use_floats := false] (arith := binary32)

/--
error: the option `cega.arithmetic` does not name an arithmetic:
  `double` is not a FloatLib binary format; the arithmetic of `cega` is `"exact"` or a format such as `binary16`, `binary32`, `binary64`, `binary128`, `FloatFormat.ieee e f` for `e` exponent bits and `f` fraction bits, or `"binary(p := 113, emax := 16383)"` for a precision and a largest exponent. A format is a closed term: the variables and hypotheses of the goal are not in its scope.
    Unknown identifier `double`
-/
#guard_msgs in
set_option cega.arithmetic "double" in
/-- An option that names no arithmetic stops the call. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x ≤ 2.72 := by
  cega

/--
error: `cega [batch := 3]` decides the family of statements as it is written, by evaluating its decision procedure; it encloses no real expression, so it has no arithmetic to switch and takes no configuration items. Write `cega [batch := 3]`. A family stated with FloatLib's floats is decided the same way, with the arithmetic of its own statement.
-/
#guard_msgs in
/-- A batch decides its statement as it is written and has no arithmetic to switch. -/
example : ∀ i : Fin 6, i.val < 6 := by
  cega [batch := 3, use_floats]

/-- `use_floats := false` on a batch is the batch. -/
example : ∀ i : Fin 6, i.val < 6 := by
  cega [batch := 3, use_floats := false]

/-! ## A float proof and a rational proof of one statement

On `x + 1` over `[0, 1]` the rational query and the binary64 query return the same interval,
`[1, 2]`, so their certificate theorems have the same statement. Lean's auxiliary-lemma cache is
keyed on the statement. A theorem checked in a float arithmetic stays outside that cache, so
neither proof stands in for the other, whichever comes first. -/

/-- The statement of the certificate theorem of the plain query of `x + 1` on `[0, 1]` in
`arithmetic`, and whether its proof computes in a float format: the theorem holds the query as
the kernel reduced it, which names the format of every float operation. -/
meta def queryProof (arithmetic : Elaboration.Arithmetic) :
    Lean.Elab.TermElabM (Lean.Expr × Bool) := do
  let box : List RationalInterval := [RationalInterval.ofBounds 0 1 (by decide)]
  let expr : Expr (Fin 1) := .add (.var 0) (.nat 1)
  let some result ← Elaboration.withArithmetic arithmetic
      (Elaboration.runBoxQuery .enclose .plain {} box expr)
    | throwError "the query found no enclosure"
  let some name := result.proof.constName?
    | throwError "the proof of the query is not an auxiliary theorem"
  let info ← Lean.getConstInfo name
  let float := (info.value? (allowOpaque := true)).any fun value ↦
    (value.find? (·.isConstOf ``FloatFormat.ieee)).isSome
  return (info.type, float)

/-- info: one statement: true; rational query first: its proof is float: false, then the float
query: true; float query first: its proof is float: true, then the rational query: false -/
#guard_msgs (whitespace := lax) in
run_elab do
  let double : Elaboration.Arithmetic := .float "binary64" 11 52
  let (same, first, second) ← Lean.withoutModifyingEnv do
    let (exactType, exactFloat) ← queryProof .exact
    let (floatType, floatFloat) ← queryProof double
    return (exactType == floatType, exactFloat, floatFloat)
  let (third, fourth) ← Lean.withoutModifyingEnv do
    let (_, floatFloat) ← queryProof double
    let (_, exactFloat) ← queryProof .exact
    return (floatFloat, exactFloat)
  Lean.logInfo m!"one statement: {same}; rational query first: its proof is float: {first}, then \
    the float query: {second}; float query first: its proof is float: {third}, then the rational \
    query: {fourth}"

/-! ## The theorems behind the tactic

The check and the query that `cega [use_floats]` builds, and the theorems that it applies, on
`x * (1 - x)` over `[0, 1]` in binary64. `decide +kernel` has the kernel evaluate each check as it
is written. -/

/-- The box `[0, 1]`. -/
def unitBox : Fin 1 → RationalInterval := fun _ ↦ .ofBounds 0 1 (by norm_num)

/-- The expression `x * (1 - x)`. -/
def parabola : Expr (Fin 1) := .mul (.var 0) (.sub (.nat 1) (.var 0))

/-- `boundOn_of_refutes` turns a binary64 refutation of the negated bound into a proof of
`x * (1 - x) ≤ 13 / 50` on `[0, 1]`. With `atom 6`, FloatLib bisects pieces whose enclosure does
not settle the bound, at most six times along each branch. The kernel checks the refutation. -/
theorem by_refutation : ∀ x ∈ RationalInterval.boxDomain unitBox,
    parabola.eval (fun i ↦ x i) ≤ ((13 / 50 : ℚ) : ℝ) :=
  boundOn_of_refutes (.binary .binary64) (floatConfig .binary64) (r := .atom 6) (13 / 50)
    (by decide +kernel)

/-- `boundOn_of_check`: after six bisections the binary64 enclosure of the float query has an upper
end of at most `13 / 50`, which the kernel evaluates, so the real bound holds on the box. -/
theorem by_hand : ∀ x ∈ RationalInterval.boxDomain unitBox,
    parabola.eval (fun i ↦ x i) ≤ ((13 / 50 : ℚ) : ℝ) :=
  boundOn_of_check (encloseBoxFloat? FloatFormat.binary64 rfl [0, 0, 0, 0, 0, 0] unitBox parabola)
    (13 / 50) (by decide +kernel)

/-- `enclosedOn_of_check`: the same enclosure gives both ends. -/
theorem by_hand_two_sided : ∀ x ∈ RationalInterval.boxDomain unitBox,
    parabola.eval (fun i ↦ x i) ∈ Set.Icc ((0 : ℚ) : ℝ) ((13 / 50 : ℚ) : ℝ) :=
  enclosedOn_of_check
    (encloseBoxFloat? FloatFormat.binary64 rfl [0, 0, 0, 0, 0, 0] unitBox parabola) 0 (13 / 50)
    (by decide +kernel)

/-- `encloseBoxFloat?_isSome_iff`: the query on the whole box has a result, because FloatLib's
diagnosis of it reports no obstruction. -/
theorem query_isSome :
    (encloseBoxFloat? FloatFormat.binary64 rfl [] unitBox parabola).isSome = true :=
  encloseBoxFloat?_isSome_iff.mpr (by decide +kernel)

/-- `ends_of_encloseBoxFloat?`: the two ends of that result are finite binary64 numbers. The
premise is `query_isSome`. -/
example {a : RationalInterval.EnclosureAttempt (ℝ^1) (RationalInterval.boxDomain unitBox)
      (fun x ↦ parabola.eval fun i ↦ x i)}
    (h : encloseBoxFloat? FloatFormat.binary64 rfl [] unitBox parabola = some a) :
    ∃ l u : Model FloatFormat.binary64, Model.isFinite l = true ∧ Model.isFinite u = true ∧
      (a.interval.lo : ℝ) = Model.toReal l ∧ (a.interval.hi : ℝ) = Model.toReal u :=
  ends_of_encloseBoxFloat? h

/-- The square of `10 ^ 200` has no binary64 enclosure: FloatLib's diagnosis rejects the product,
whose enclosure has an end past the largest binary64 number, and the message of `pow_overflow`'s
binary64 attempt reports that product. -/
example :
    (floatObstruction? FloatFormat.binary64 [] (fun i : Fin 0 ↦ i.elim0)
      (.mul (.pow (.nat 10) 200) (.pow (.nat 10) 200))).any
      (· matches .rejected (.binary .mul _ _) _) = true := by
  decide +kernel

/--
info: 'CAS.Examples.CEGA.Floats.by_refutation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms by_refutation

/--
info: 'CAS.Examples.CEGA.Floats.by_hand' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms by_hand

/--
info: 'CAS.Examples.CEGA.Floats.by_hand_two_sided' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms by_hand_two_sided

end CAS.Examples.CEGA.Floats

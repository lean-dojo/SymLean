/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedBivariate
public import CAS.Cert.Shard
public meta import CAS.Cert.Shard

/-!
# The exact integral of a squared residual on one cell

## Motivation

Does the test of [PackedBivariate](../../Numerics/PackedBivariate.lean) compute the integral
of the square of a residual with derivatives and a product, and does the kernel refuse a
bound that is too small by one unit?

## The idea

The data are invented: on one cell, the polynomial `U` of degree 2 in each variable that
interpolates `u = sin (3 x + 2 y) + cos (5 x - y) / 2`, and the interpolant `F` of
`f = ν (u_xx + u_yy) - u u_x` with `ν = 2 ^ -1`, with coefficients rounded to multiples of
`2 ^ -10`. The residual expression `R` is `2 ^ 21 (ν (U_xx + U_yy) - U U_x - F)` in the
coordinates of the reference cell. A program outside this repository computed `D` times the
integral of `R ^ 2` exactly; the kernel recomputes it from the two stored rows.

## Main results

* `residual_le` (one example): the integral over the unit square of the square of the real
  function of `R` is at most the stored number `bound` divided by `D`.
* `cellCheck_false` (one example): with `bound - 1` the test fails, so `bound` is the exact
  value. `sizes_zero`: the sizes are refused with `D = 0`.

## Relations

An instance of `BivExpr.sq_integral_le_div`, which is `BivExpr.sq_integral_le` with the bound
divided by `D`. Meshes with many cells store one row per cell in files and test the cells in
shards ([Shard](../../Cert/Shard.lean)).

## Scope

One invented cell.
-/

@[expose] public section

namespace CAS.Examples.Numerics.PackedBivariate

open CAS.Cert CAS.Numerics

/-- The packed row of the field: 27 slots of 140 bits, with the coefficient of
`x ^ i * y ^ j` in slot `i + 9 * j`. -/
def u : ℕ → ℕ :=
  pinned_hex% 140 27 27 972
    "f06c6d3264b7f1ff49aee08ecaaa829165a7b6322d6c3db80a3f2c86f1ba3b02"
    "00000000000000000000000000000000287\n\
    0000000000000000000000000000000012c\n\
    ffffffffffffffffffffffffffffffffd73\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000b85\n\
    fffffffffffffffffffffffffffffffecc9\n\
    ffffffffffffffffffffffffffffffff934\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    ffffffffffffffffffffffffffffffff7e5\n\
    000000000000000000000000000000000f8\n\
    00000000000000000000000000000000e22\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n"

/-- The packed row of the right-hand side: 27 slots of 140 bits, with the coefficient of
`x ^ i * y ^ j` in slot `i + 9 * j`. -/
def f : ℕ → ℕ :=
  pinned_hex% 140 27 27 972
    "114a4a34c1bf8b5e49daedaa98503155137b59985fabaac38d74d42eb9dff719"
    "fffffffffffffffffffffffffffffffd4b2\n\
    0000000000000000000000000000000818f\n\
    fffffffffffffffffffffffffffffff9e7b\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    fffffffffffffffffffffffffffffff91a3\n\
    000000000000000000000000000000143b4\n\
    fffffffffffffffffffffffffffffff7d7b\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000006e11\n\
    ffffffffffffffffffffffffffffffe7910\n\
    00000000000000000000000000000011640\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n\
    00000000000000000000000000000000000\n"

/-- The residual `2 ^ 21 (ν (u_xx + u_yy) - u u_x - f)` in the reference coordinates: variable
`0` is the field and variable `1` the right-hand side. -/
def R : BivExpr :=
  (.add (.smul (1024) (.add (.dx (.dx (.var 0))) (.dy (.dy (.var 0))))) (.add (.smul (-2)
    (.mul (.var 0) (.dx (.var 0)))) (.smul (-2048) (.var 1))))

/-- The stored rows. -/
def rows (v : ℕ) : ℕ := cond (Nat.beq v 0) (u 0) (f 0)

/-- The common multiple of the denominators. -/
def D : ℕ := 908107200

/-- `D` times the integral of the squared residual, computed by a program outside this
repository. -/
def bound : ℕ :=
  249397788113817857109024

/-- The sizes of the check fit. -/
theorem sizes : BivExpr.sizesOk 140 9 3 27 20 524288 D (.mul R R) = true := by
  decide +kernel

/-- With `D = 0` the test of the sizes fails: a bound for `0` times an integral says nothing. -/
theorem sizes_zero : BivExpr.sizesOk 140 9 3 27 20 524288 0 (.mul R R) = false := by
  decide +kernel

/-- The test of the cell passes. -/
theorem cellCheck : BivExpr.sqCheck 140 9 3 27 20 D 2 rows R bound = true := by decide +kernel

/-- With the bound lowered by one the test fails: `bound` is the exact value. -/
theorem cellCheck_false : BivExpr.sqCheck 140 9 3 27 20 D 2 rows R (bound - 1) = false := by
  decide +kernel

/-- **The squared residual of the cell.** The integral over the unit square of the square of
the real function of `R`, built from the polynomials of the two stored rows with the partial
derivatives of `R`, is at most `bound / D`. One invented example. -/
theorem residual_le :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        BivExpr.eval 9 27 (fun v ↦ rowCoef 140 27 (rowAt rows 2 v)) R x y ^ 2 ≤
      (bound : ℝ) / D :=
  BivExpr.sq_integral_le_div sizes (by norm_num) cellCheck

end CAS.Examples.Numerics.PackedBivariate

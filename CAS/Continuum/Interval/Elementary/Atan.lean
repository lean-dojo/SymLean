/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.DyadicHull
public import FloatLib.Numerics.Enclosure.Interval.ElementaryProof

/-!
# Arctangent enclosures from FloatLib

`atanRangeWith I terms` is FloatLib's arctangent enclosure of `I`, from the point enclosures of
its endpoints with `terms + 1` terms of the series in each reduced argument. `atanRange I` uses
the degree `16`, so `17` terms, and rounds outward to a 128-bit dyadic grid. `atanRangeWith_sound`
and `atanRange_sound` show that they contain `Real.arctan x` for every `x ∈ I`.

## Implementation notes

The algorithm and its proof are FloatLib's. `Real.arctan` is monotone, so `Interval.atanBounds`
evaluates the point enclosure `Enclosure.atan` at the two endpoints. The point enclosure uses
odd symmetry, `arctan x = π / 2 - arctan (1 / x)` for `x > 1` and
`arctan x = π / 4 + arctan ((x - 1) / (x + 1))` for `1 / 2 < x ≤ 1`, so that the series DLMF
4.24.3 is summed only at arguments of absolute value at most `1 / 2`, with a geometric bound on
its tail; `π / 4` is Machin's `4 arctan (1 / 5) - arctan (1 / 239)`. FloatLib proves the tail
bound and takes Machin's identity from Mathlib.

We call `Interval.atanBounds` directly. Its series `Enclosure.atanTaylor`
is the binary splitting `Taylor.atan` by definition, which composes integer Horner blocks and
normalizes once, so the kernel evaluates it as it stands.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, <https://github.com/lean-dojo/FloatLib>.
* NIST Digital Library of Mathematical Functions, §4.24 Inverse Trigonometric Functions: Further
  Properties, Version 1.2.8 (2026-09-15), <https://dlmf.nist.gov/4.24>. Equation (4.24.3), the
  series of `arctan z` for `|z| ≤ 1`.
* David H. Bailey, Jonathan M. Borwein, Peter B. Borwein and Simon Plouffe, "The Quest for Pi",
  *The Mathematical Intelligencer* 19 (1997), pp. 50-57, <https://doi.org/10.1007/BF03024340>.
  Section 2 for Machin's formula.
-/

@[expose] public section

namespace CAS.Continuum

namespace RationalInterval

/-- FloatLib's arctangent enclosure with `terms` as the series degree. -/
def atanRangeWith (I : RationalInterval) (terms : ℕ) : RationalInterval :=
  ofFloatLib (FloatLib.Numerics.Interval.atanBounds I.toFloatLib terms)
    (ordered_of_containsReal (FloatLib.Numerics.Interval.containsReal_atanBounds
      I.toFloatLib terms ((I.toFloatLib_containsReal_iff _).mpr I.lo_memReal)))

/-- `atanRangeWith I terms` contains `Real.arctan x` for every `x ∈ I`. -/
theorem atanRangeWith_sound (I : RationalInterval) (terms : ℕ)
    {x : ℝ} (hx : I.MemReal x) :
    (atanRangeWith I terms).MemReal (Real.arctan x) :=
  (memReal_ofFloatLib_iff _ _ _).mpr
    (FloatLib.Numerics.Interval.containsReal_atanBounds I.toFloatLib terms
      ((I.toFloatLib_containsReal_iff x).mpr hx))

/-- FloatLib's arctangent enclosure with the degree `16` (`17` terms), rounded outward on a
128-bit binary grid. -/
def atanRange (I : RationalInterval) : RationalInterval :=
  dyadicHull 128 (atanRangeWith I 16)

/-- `atanRange I` contains `Real.arctan x` for every `x ∈ I`. -/
theorem atanRange_sound (I : RationalInterval)
    {x : ℝ} (hx : I.MemReal x) :
    (atanRange I).MemReal (Real.arctan x) :=
  dyadicHull_sound 128 (atanRangeWith_sound I 16 hx)

end RationalInterval
end CAS.Continuum

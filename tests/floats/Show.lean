/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
import CAS
import Bounds

/-!
# The arithmetic of the proofs that a build produced

For each theorem of `Bounds`, this file reads the proof that Lake built and prints the backend of
FloatLib that it computes with: `ieee(e,f)` when the ends of its intervals are numbers of the IEEE
format with `e` exponent bits and `f` fraction bits, `exact` when they are exact rationals, and
`other` when the proof computes no enclosure. A float backend names its format,
`FloatFormat.ieee e f`: FloatLib's check with the ends `CAS.CEGA.Check.Endpoints.binary`, and the
float query `CAS.CEGA.encloseBoxFloat?`, which computes with the same ends. An exact proof names
the ends `CAS.CEGA.Check.Endpoints.exact` of FloatLib's check, or the rational query of the
planner (`CAS.CEGA.encloseBoxWith?`, its subdivided form, or an attempt that the kernel reduced).
It follows the auxiliary theorems of `Bounds`, where `cega` keeps its certificates and FloatLib's
check its decisions. The last word is `standard` when every theorem depends only on `propext`,
`Classical.choice` and `Quot.sound`. `tests/floats/run.sh` compares the line.
-/

open Lean

/-- The exponent and fraction widths of the float format in `value`, if it names one. -/
def floatWidths? (value : Expr) : Option (Nat × Nat) := do
  let format ← value.find? fun term ↦
    term.isAppOfArity ``FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.ieee 4
  let width (term : Expr) : Option Nat := term.rawNatLit? <|> term.nat?
  return (← width format.getAppArgs[0]!, ← width format.getAppArgs[1]!)

/-- The constants that name an exact backend: the ends of FloatLib's check in exact arithmetic,
and the rational queries of the planner. -/
def exactBackends : List Name :=
  [``CAS.CEGA.Check.Endpoints.exact, ``CAS.CEGA.encloseBoxWith?,
    ``CAS.CEGA.encloseBoxSubdividedAtWith?, ``CAS.Continuum.RationalInterval.EnclosureAttempt.mk]

/-- The backend of FloatLib in the proof of `name`, through the declarations of the module `Bounds`
that the proof uses: the widths of its float format, or `exact`, or `other`. -/
def arithmeticOf (name : Name) : CoreM String := do
  let env ← getEnv
  let some bounds := env.getModuleIdx? `Bounds | throwError "the module Bounds is not imported"
  let mut pending := #[name]
  let mut visited : NameSet := {}
  let mut exact := false
  while !pending.isEmpty do
    let current := pending.back!
    pending := pending.pop
    let some value := (env.find? current).bind (·.value? (allowOpaque := true)) | continue
    if let some (e, f) := floatWidths? value then
      return s!"ieee({e},{f})"
    for constant in value.getUsedConstants do
      if exactBackends.contains constant then
        exact := true
      if env.getModuleIdxFor? constant == some bounds && !visited.contains constant then
        visited := visited.insert constant
        pending := pending.push constant
  return if exact then "exact" else "other"

run_meta do
  let names := [``bare, ``closed, ``configured, ``query, ``fast, ``floatsOff, ``floatsOn, ``quad,
    ``queryExact, ``integral, ``finite, ``viaCas]
  let mut line := ""
  let mut standard := true
  for name in names do
    line := line ++ s!"{name}={← arithmeticOf name} "
    for used in ← collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains used do
        standard := false
  IO.println (line ++ (if standard then "axioms=standard" else "axioms=OTHER"))

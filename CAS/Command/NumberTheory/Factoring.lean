/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.NumberTheory.Basic
public meta import CAS.Tactic.RouteRegistry

/-!
# Number theory commands without a built-in backend

SymLean recognizes `primeQ`, `moebiusMu` and `factorInteger`, but does not compute their values.
Each command tries the registered backends and reports that it is unavailable if none answers.
-/

public meta section

namespace CAS.Command

open Lean Elab Command

/-- `#cas [factorInteger] n` is unavailable: SymLean does not compute prime factorizations. -/
syntax (name := casFactorIntegerCommand) "#cas" "[" &"factorInteger" "]" term : command

/-- Try the registered backends for `operation`; there is no built-in computation. -/
def NumberTheory.runBackend (operation : Name) (input : Syntax) : CommandElabM Unit := do
  unless ← Tactic.RouteRegistry.runCommandBackends operation input do
    throwErrorAt input "{operation} is not available in SymLean"

elab_rules : command
  | `(#cas [factorInteger] $n:term) => NumberTheory.runBackend `factorInteger n

end CAS.Command

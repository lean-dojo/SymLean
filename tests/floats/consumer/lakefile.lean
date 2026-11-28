import Lake

open Lake DSL

/-! A package that requires SymLean and takes the arithmetic of the `cega` calls of its modules
from the command line. `lake build` computes with exact rationals, the default of SymLean, and
`lake build -R -Karithmetic=binary64` with binary64 floats; no Lean file names the arithmetic.
`run.sh` puts SymLean next to the package. -/

/-- The arithmetic of the `cega` calls of this package: the value of `-Karithmetic=…`, such as
`binary64` or `binary128`, and exact arithmetic without it. -/
def arithmetic : String := (get_config? arithmetic).getD "exact"

package consumer

require SymLean from ".." / "symlean"

lean_lib Bounds where
  leanOptions := #[⟨`weak.cega.arithmetic, arithmetic⟩]

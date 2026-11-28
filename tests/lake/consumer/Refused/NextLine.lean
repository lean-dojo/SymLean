module

public import CAS.IncludeStr

/-! A path that an operator on the next line continues, which the check refuses. -/

/-- `p plus s` appends `s` to the path `p`. -/
public def appendPath (p : System.FilePath) (s : String) : System.FilePath :=
  System.FilePath.mk (p.toString ++ s)

@[inherit_doc] infixl:65 " plus " => appendPath

/-- Lean reads the operator on the next line as part of the path. -/
public def nextLine : String :=
  include_str "data"
  plus ".txt"

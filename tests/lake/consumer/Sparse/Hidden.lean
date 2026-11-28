module

public import CAS.IncludeStr

/-! A module that no glob of `Sparse` lists, which Lake builds as part of `Sparse`. -/

/-- The text of `hidden.txt`, which `run.sh` writes. No glob of `Sparse` lists this module, but
Lake builds it as part of `Sparse`, whose root is a prefix of its name. -/
public def hidden : String := include_str "hidden.txt"

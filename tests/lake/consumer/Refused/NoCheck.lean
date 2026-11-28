module

/-! A module that embeds a file without importing the check, which the facet refuses. -/

/-- A module that embeds a file but does not import the check. -/
public def unchecked : String := include_str "data.txt"

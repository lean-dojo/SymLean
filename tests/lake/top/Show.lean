import CAS
import Probe.Single
import Top.Data

/-! Prints the texts of `top`, of the consumer and of SymLean, two levels above SymLean. -/

#eval IO.println s!"top={topData} single={single} cas={casData}"

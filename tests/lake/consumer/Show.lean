import CAS
import Probe.Single
import Probe.Multi
import Probe.PlusMinus
import Probe.Coerced

/-! Prints the texts of the probes and of SymLean, for the tracking tests of `run.sh`. -/

#eval IO.println s!"single={single} multi={multi} plusminus={plusMinus} coerced={coerced} \
  cas={casData}"

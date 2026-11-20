import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.GammaIndependence.PeriodMapZEqCast
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.Imports

set_option backward.isDefEq.respectTransparency false

namespace CrystallineSemistableComparison

/- English proof (translation)
The claim follows from `phi_of inj`.
-/
theorem phi : FrobeniusComparison := phi_of inj

end CrystallineSemistableComparison

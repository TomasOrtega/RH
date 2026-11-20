import Formalism.MonomialMeanResidues.MonomialMean
import Formalism.MonomialMeanResidues.BetaLogMean
import Mathlib
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Formalism.MonomialMeanResidues.MonomialMeanProofs.SubmoduleSlopeLowerOfFiltration
import Formalism.MonomialMeanResidues.MonomialMeanProofs.SpanEqTopAndRankOfLinearIndependent

namespace Formalism.HermiteSiegelSlopes

/- English proof (translation)
The claim follows from `base_change_slope`.
-/
theorem baseChange : BaseChange := base_change_slope

end Formalism.HermiteSiegelSlopes

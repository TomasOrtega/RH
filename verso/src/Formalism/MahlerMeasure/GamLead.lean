import Formalism.MahlerMeasure.FinalM
import Formalism.MahlerMeasure.MahlerMeasureProofs.GamDeg
import Formalism.MahlerMeasure.MahlerMeasureProofs.GamLead
import Formalism.MahlerMeasure.MahlerMeasureProofs.GamInt

namespace Formalism.GM.Top
open Formalism.GM
/- English proof (translation)
The claim follows from `gamma_degree_bound`.
-/
theorem gamDeg : M.GamDeg := gamma_degree_bound
/- English proof (translation)
The claim follows from `gamma_leading_term`.
-/
theorem gamLead : M.GamLead := gamma_leading_term
/- English proof (translation)
The claim follows from `gamma_integrality`.
-/
theorem gamInt : M.GamInt := gamma_integrality
end Formalism.GM.Top

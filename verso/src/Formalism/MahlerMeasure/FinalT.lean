import Formalism.MahlerMeasure.MahlerMeasureProofs.BadCrit
import Formalism.MahlerMeasure.MahlerMeasureProofs.MeanGam
import Formalism.MahlerMeasure.GamLead
import Formalism.MahlerMeasure.CoarseLevelSlackInequalities

namespace Formalism.GM.Top
open Formalism.GM
/- English proof (translation)
The claim follows from `bad_criterion_holds`.
-/
theorem badCrit : M.BadCrit := bad_criterion_holds
/- English proof (translation)
The claim follows from `meanGam_of gamDeg gamLead gamInt windowFullAP`.
-/
theorem meanGam : M.MeanGam := meanGam_of gamDeg gamLead gamInt windowFullAP
end Formalism.GM.Top

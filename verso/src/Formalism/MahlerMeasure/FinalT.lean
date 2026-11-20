import Formalism.MahlerMeasure.MahlerMeasureProofs.BadCrit
import Formalism.MahlerMeasure.MahlerMeasureProofs.MeanGam
import Formalism.MahlerMeasure.GamLead
import Formalism.MahlerMeasure.CoarseLevelSlackInequalities

namespace Formalism.GM.Top
open Formalism.GM
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem badCrit : M.BadCrit := bad_criterion_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem meanGam : M.MeanGam := meanGam_of gamDeg gamLead gamInt windowFullAP
end Formalism.GM.Top

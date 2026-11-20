import Formalism.MahlerMeasure.MahlerMeasureProofs.WindowAP
import Formalism.MahlerMeasure.MahlerMeasureProofs.WindowMeanAP
import Formalism.MahlerMeasure.FinalD

namespace Formalism.GM.Top
open Formalism.GM
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem windowCountAP : WindowCountAP := window_count_progression
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem discsDisjointAP : DiscsDisjointAP := root_discs_disjoint_progression
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem windowMeanAP : WindowMeanAP := windowMeanAP_of windowCountAP discsDisjointAP
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem windowFullAP : WindowFullAP := windowFullAP_of valuation_window_lower_bound windowMeanAP
end Formalism.GM.Top

import Formalism.MahlerMeasure.MahlerMeasureProofs.WindowAP
import Formalism.MahlerMeasure.MahlerMeasureProofs.WindowMeanAP
import Formalism.MahlerMeasure.FinalD

namespace Formalism.GM.Top
open Formalism.GM
/- English proof (translation)
The claim follows from `window_count_progression`.
-/
theorem windowCountAP : WindowCountAP := window_count_progression
/- English proof (translation)
The claim follows from `root_discs_disjoint_progression`.
-/
theorem discsDisjointAP : DiscsDisjointAP := root_discs_disjoint_progression
/- English proof (translation)
The claim follows from `windowMeanAP_of windowCountAP discsDisjointAP`.
-/
theorem windowMeanAP : WindowMeanAP := windowMeanAP_of windowCountAP discsDisjointAP
/- English proof (translation)
The claim follows from `windowFullAP_of valuation_window_lower_bound windowMeanAP`.
-/
theorem windowFullAP : WindowFullAP := windowFullAP_of valuation_window_lower_bound windowMeanAP
end Formalism.GM.Top

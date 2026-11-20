import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRTopActCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRTopActAlg

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

/- English proof (translation)
The claim follows from `TopAct.gTRTopAct_of_cut quadratic_top_algebra_holds`.
-/
theorem top_action_on_gauge_holds : GTRTopAct := TopAct.gTRTopAct_of_cut quadratic_top_algebra_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

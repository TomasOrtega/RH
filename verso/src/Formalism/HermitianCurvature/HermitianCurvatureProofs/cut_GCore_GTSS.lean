import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLocal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSConst
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadT
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSAdj

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

/- English proof (translation)
Introduce `hA hR` and use `gTSS_of_cut (gTSSLocal_of_radT hR) hA SSC.second_shift_constant SSPh.second_shift_phase_holds`.
-/
theorem gTSS_of_adj_radT : GTSSAdjPt → GTCLRadT → GTSS := fun hA hR =>
  gTSS_of_cut (gTSSLocal_of_radT hR) hA SSC.second_shift_constant SSPh.second_shift_phase_holds

/- English proof (translation)
Introduce `hA` and use `gTSS_of_adj_radT hA radial_torus_local_holds`.
-/
theorem gTSS_of_adj : GTSSAdjPt → GTSS := fun hA => gTSS_of_adj_radT hA radial_torus_local_holds

/- English proof (translation)
The claim follows from `gTSS_of_adj second_shift_adjoint_pointwise`.
-/
theorem second_shift_gauge_holds : GTSS := gTSS_of_adj second_shift_adjoint_pointwise

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

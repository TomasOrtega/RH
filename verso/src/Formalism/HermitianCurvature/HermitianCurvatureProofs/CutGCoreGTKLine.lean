import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLEig
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLAtMost
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLIsoAlg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLLieGrp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLExistsOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferKPt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferKAsm

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lie_group_existence_holds : KLExists := lie_existence_of_iso_group KLIso.lie_algebra_isomorphism_holds lie_group_realization

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gauge_kappa_line_holds : GTKLine := gTKLine_of_cut lie_eigenvalue_holds lie_weight_at_most_holds lie_group_existence_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gauge_kappa_holds : GTKap := GTK.gauge_kappa_of_point_line gauge_kappa_pointwise_holds gauge_kappa_line_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeC

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

def GTConnOfLeaves : Prop := GTCLocal → GTCReal → GTCCurv → GTCHol → GTCAnnulus → GTConn

/- English proof (translation)
Introduce `hL hR hC hH hA` and use `gTConn_of_cut hL (gTCPhase_of_cut hR hC hH hA torus_parameter) gauge_transform_holds`.
-/
theorem gTConn_of_leaves : GTConnOfLeaves := fun hL hR hC hH hA =>
  gTConn_of_cut hL (gTCPhase_of_cut hR hC hH hA torus_parameter) gauge_transform_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

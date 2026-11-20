import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvPoly
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvScal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvRTT
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvTop

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem curvature_polynomial_holds : GTCCurvPoly := curvature_polynomial_of_scalar curvature_scalar_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem curvature_identity_holds : GTCCurvId :=
  gTCCurvId_of_cut curvature_polynomial_holds curvature_radial_torus_holds curvature_block_form_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem top_normal_form_of_curvature : GTRTopNF := gTRTopNF_of_curvPoly curvature_polynomial_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

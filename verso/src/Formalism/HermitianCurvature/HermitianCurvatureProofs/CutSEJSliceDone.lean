import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSliceAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SpectralSobolevSecondOrder
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSMeas
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSWordNF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JslHsInnerSelfNorm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSELeibnizClsC

namespace Formalism.FourierDecayAlt.P.CutSE

/- English proof (translation)
The claim follows from `jSliceGenC_of_sob2_meas_locality spectral_sobolev_second_order spectral_measurability (jSL2Loc_of spectral_word_normal_form hR)`.
-/
theorem jSliceGenC_of_radLoc (hR : JSRadLoc) : JSliceGenC :=
  jSliceGenC_of_sob2_meas_locality spectral_sobolev_second_order spectral_measurability (jSL2Loc_of spectral_word_normal_form hR)

/- English proof (translation)
The claim follows from `leibnizCls_of_jSliceC (jSliceGenC_of_radLoc hR)`.
-/
theorem leibnizCls_of_radLoc (hR : JSRadLoc) : LeibnizCls :=
  leibnizCls_of_jSliceC (jSliceGenC_of_radLoc hR)

/- English proof (translation)
The claim follows from `densSmoothCls_of_jSliceC (jSliceGenC_of_radLoc hR)`.
-/
theorem densSmoothCls_of_radLoc (hR : JSRadLoc) : DensSmoothCls :=
  densSmoothCls_of_jSliceC (jSliceGenC_of_radLoc hR)

end Formalism.FourierDecayAlt.P.CutSE

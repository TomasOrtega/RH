import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSETopHer
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEOneLetterDens
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSliceDone
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSRadLoc
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialIdentityOfSpectralData

namespace Formalism.FourierDecayAlt.P.CutSE

/- English proof (translation)
The claim follows from `leibnizCls_of_radLoc spectral_radial_locality`.
-/
theorem leibniz_class : LeibnizCls := leibnizCls_of_radLoc spectral_radial_locality

/- English proof (translation)
The claim follows from `densSmoothCls_of_radLoc spectral_radial_locality`.
-/
theorem density_smooth_class : DensSmoothCls := densSmoothCls_of_radLoc spectral_radial_locality

/- English proof (translation)
The claim follows from `thmPActualCpt_of_leaves (one_letter_density_estimate leibniz_class density_smooth_class) density_smooth_class (radDecay_of_spec h)`.
-/
theorem thmPActualCpt_of_spec (h : RDIdentSpec) : Formalism.FourierDecayAlt.P5.ThmPActualCpt :=
  thmPActualCpt_of_leaves (one_letter_density_estimate leibniz_class density_smooth_class) density_smooth_class
    (radDecay_of_spec h)

end Formalism.FourierDecayAlt.P.CutSE

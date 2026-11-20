import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSNicePoly

namespace Formalism.FourierDecayAlt.P.CutSE

/- English proof (translation)
The claim follows from `rDSOpRGrp_of_nice spectral_nice_polynomial`.
-/
theorem spectral_right_group_action : RDSOpRGrp := rDSOpRGrp_of_nice spectral_nice_polynomial

/- English proof (translation)
The claim follows from `rDSOpRvGrp_of_nice spectral_nice_polynomial`.
-/
theorem spectral_adjoint_right_group : RDSOpRvGrp := rDSOpRvGrp_of_nice spectral_nice_polynomial

end Formalism.FourierDecayAlt.P.CutSE

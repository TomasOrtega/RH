import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPolyProp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSAGrp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSARad
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSALoc

namespace Formalism.FourierDecayAlt.P.CutSE

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem spectral_operator_A : RDSOpA :=
  rDSOpA_of_parts spectral_polynomial_property spectral_group_action spectral_radial_action spectral_action_locality

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem spectral_operator_A_adjoint : RDSOpAv :=
  rDSOpAv_of_parts spectral_polynomial_property spectral_group_action spectral_radial_action spectral_action_locality

end Formalism.FourierDecayAlt.P.CutSE

import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentSpecAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpADone
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPAdj
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSQQAdj
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSXiTest
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPairDone
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE_TopSpec

namespace Formalism.FourierDecayAlt.P.CutSE

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rDIdentSpec_of_R (hR : RDSOpR) (hRv : RDSOpRv) : RDIdentSpec :=
  rDIdentSpec_of_open spectral_operator_A_adjoint hR hRv spectral_operator_A spectral_pairing_adjoint spectral_quadratic_adjoint spectral_xi_test spectral_pairing_identity

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmPActualCpt_of_R (hR : RDSOpR) (hRv : RDSOpRv) : Formalism.FourierDecayAlt.P5.ThmPActualCpt :=
  thmPActualCpt_of_spec (rDIdentSpec_of_R hR hRv)

end Formalism.FourierDecayAlt.P.CutSE

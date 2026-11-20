import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjFund
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjCont
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjInt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

/- English proof (translation)
The claim follows from `adjComm_of_parts fundamental_domain_group adjoint_continuity_holds adjoint_integral_identity_holds`.
-/
theorem adjoint_commutation_holds : AdjComm := adjComm_of_parts fundamental_domain_group adjoint_continuity_holds adjoint_integral_identity_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS

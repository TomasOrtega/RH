import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibOps
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibBd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibVLin
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibExp

namespace Formalism.FourierDecayAlt.P.CutBP

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem leibniz_vector_estimate_holds : NFLeibV :=
  nfLeibV_of (nfLeibOps_of leibniz_expansion_holds) leibniz_bound_holds vector_linearity_holds

end Formalism.FourierDecayAlt.P.CutBP

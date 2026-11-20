import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocOpAdj
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocToolsOp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocToolsAgree
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocToolsTheta

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem local_operator_transfer_holds : JALocOp :=
  jALocOp_of_tools LT.operator_in_class_holds LT.agreement_on_domain_holds LT.theta_transfer_apply_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jALocAdj_of_adjComm (h : FFS.AdjComm) : JALocAdj :=
  jALocAdj_of_tools LT.operator_in_class_holds LT.agreement_on_domain_holds (LT.thetaJ_of_adjComm h)

end Formalism.FourierDecayAlt.P.CutMP.JA

end

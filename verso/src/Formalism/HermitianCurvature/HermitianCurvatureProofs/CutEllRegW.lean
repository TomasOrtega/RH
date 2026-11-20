import Formalism.UnipotentAdelicQuotients.EllRegCheck
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEllRegBridge

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

/- English proof (translation)
The claim follows from `elliptic_regularity_transfer_holds ZetaZeros.D.EllReg.elliptic_regularity_of_parts`.
-/
theorem elliptic_regularity_weighted : EllRegW := elliptic_regularity_transfer_holds ZetaZeros.D.EllReg.elliptic_regularity_of_parts

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

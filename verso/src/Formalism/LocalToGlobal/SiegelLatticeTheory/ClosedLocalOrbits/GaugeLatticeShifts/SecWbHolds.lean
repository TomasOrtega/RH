import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacExGoodOfN
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem secWb_holds : SecWb := fun k r z z' hk hz hz' hT hT' =>
  Formalism.FourierDecayAlt.P.SettingConstruction.sectionExists k r z z' hk hz hz' hT hT'

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

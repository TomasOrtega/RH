import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SphericalFunctionFunctionalEq
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SphericalFunctionLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingExistence

namespace GlobalTheory.HCXi

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem xiExists_of_besselXiIntegrable : BesselXiIntegrable → Formalism.FourierDecayAlt.B.XiExists := fun h => h

end GlobalTheory.HCXi

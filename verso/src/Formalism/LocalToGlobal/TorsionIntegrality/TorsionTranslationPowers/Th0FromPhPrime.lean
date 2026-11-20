import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Joints
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ThetaFromPhiDerivative

namespace Formalism.L2.Th1.E

/- English proof (translation)
The claim follows from `joint_integrality`.
-/
theorem vJoint : VJoint := joint_integrality
/- English proof (translation)
The claim follows from `phi_model_eq`.
-/
theorem phWEq : PhWEq := phi_model_eq
/- English proof (translation)
The claim follows from `even_theta_half_period_in_model`.
-/
theorem inWTh0 : InWTh0 := even_theta_half_period_in_model
/- English proof (translation)
The claim follows from `theta_from_phi_derivative`.
-/
theorem th0FromPhPrime : ThetaZeroFromPhiDerivative := theta_from_phi_derivative

end Formalism.L2.Th1.E

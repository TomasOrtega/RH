import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuantumMinorExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuantumMinorCommutation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AlgebraicQuantumDeterminant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorRepresentations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliCoordinates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftDerivativeCurves
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AnisotropicColumnSums
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftTypeAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameEntries

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem algebraic_quantum_determinant : Qr.AlgDet :=
  qr_algDet_of (qr_algDetBasis_of quantum_jacobi_identity quantum_determinant_vector quantum_minor_covariance)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem capelli_hat_frame : Qr.ChatFrame := qr_chatFrame_of frame_minor

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem determinant_hat : DetHat :=
  qr_detHat_of algebraic_quantum_determinant capelli_hat_frame capelli_right_good left_right_swap

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem determinant_hat_regular : DetHatRegular := qr_detHatRegular_of determinant_hat

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem regular_to_smooth : RegularToSmooth := fun _ => determinant_hat

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem determinant_generic : DetGeneric := qr_detGeneric_of determinant_hat_regular

end Formalism.FourierDecayAlt.P

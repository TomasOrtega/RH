import Formalism.HermitianCurvature.BlockKernelPropertiesOfSteps
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CharacterOrthogonalityDual
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelQuotientFinite
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelNonzeroModulusDeterminantEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstKernelPropertiesOfHypotheses
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AddedBlockKernelSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstKernelExplicitFormula

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `second_gram_of_gram_and_modulus kernel_gram_property modulus_positive_multiplicative`.
-/
theorem second_gram_property : Formalism.FourierDecayAlt.A5.BlockKernelPosSemidef := second_gram_of_gram_and_modulus kernel_gram_property modulus_positive_multiplicative

namespace FirstKernelProperties

/- English proof (translation)
The claim follows from `first_kernel_properties_of_hypotheses first_kernel_explicit_formula integral_points_finite characterOrthogonalityDual characterOrthogonality cokernel_card_inverse_modulus second_gram_property`.
-/
theorem first_kernel_periodic_gram_parseval :
    Formalism.FourierDecayAlt.A5.SingleBlockPeriodic ∧ Formalism.FourierDecayAlt.A5.SingleBlockPosSemidef ∧ Formalism.FourierDecayAlt.A5.SingleBlockParseval :=
  first_kernel_properties_of_hypotheses first_kernel_explicit_formula integral_points_finite characterOrthogonalityDual
    characterOrthogonality cokernel_card_inverse_modulus second_gram_property

end FirstKernelProperties

/- English proof (translation)
The claim follows from `A5x6.first_kernel_periodic_of_formula first_kernel_explicit_formula`.
-/
theorem first_kernel_periodic : Formalism.FourierDecayAlt.A5.SingleBlockPeriodic := A5x6.first_kernel_periodic_of_formula first_kernel_explicit_formula

/- English proof (translation)
The claim follows from `A5x6.first_kernel_gram_of_second second_gram_property`.
-/
theorem first_kernel_gram_property : Formalism.FourierDecayAlt.A5.SingleBlockPosSemidef := A5x6.first_kernel_gram_of_second second_gram_property

/- English proof (translation)
The claim follows from `FirstKernelProperties.first_kernel_periodic_gram_parseval.2.2`.
-/
theorem first_kernel_parseval : Formalism.FourierDecayAlt.A5.SingleBlockParseval := FirstKernelProperties.first_kernel_periodic_gram_parseval.2.2

namespace FirstKernelProperties

/- English proof (translation)
Assemble the required witnesses or components as `⟨A5x6.first_theta_eq_of_equality (A5x6.first_theta_equality_of_kernel_facts first_kernel_periodic first_kernel_gram_property first_kernel_parseval added_block_kernel_support added_block_kernel_block_diagonal), A5x6.first_theta_equality_of_kernel_facts first_kernel_periodic first_ …`.
-/
theorem th1All : Formalism.FourierDecayAlt.A5.Th1Eq ∧ Formalism.FourierDecayAlt.A5.SingleBlockThetaProps := ⟨A5x6.first_theta_eq_of_equality (A5x6.first_theta_equality_of_kernel_facts first_kernel_periodic first_kernel_gram_property first_kernel_parseval
    added_block_kernel_support added_block_kernel_block_diagonal),
    A5x6.first_theta_equality_of_kernel_facts first_kernel_periodic first_kernel_gram_property first_kernel_parseval
      added_block_kernel_support added_block_kernel_block_diagonal⟩

end FirstKernelProperties

/- English proof (translation)
The claim follows from `A5x6.first_theta_eq_of_equality (A5x6.first_theta_equality_of_kernel_facts first_kernel_periodic first_kernel_gram_property first_kernel_parseval added_block_kernel_support added_block_kernel_block_diagonal)`.
-/
theorem first_theta_kernel_equality : Formalism.FourierDecayAlt.A5.Th1Eq := A5x6.first_theta_eq_of_equality (A5x6.first_theta_equality_of_kernel_facts first_kernel_periodic first_kernel_gram_property first_kernel_parseval
    added_block_kernel_support added_block_kernel_block_diagonal)

/- English proof (translation)
The claim follows from `A5x6.first_theta_equality_of_kernel_facts first_kernel_periodic first_kernel_gram_property first_kernel_parseval added_block_kernel_support added_block_kernel_block_diagonal`.
-/
theorem first_theta_equals_first_kernel : Formalism.FourierDecayAlt.A5.SingleBlockThetaProps := A5x6.first_theta_equality_of_kernel_facts first_kernel_periodic first_kernel_gram_property first_kernel_parseval
    added_block_kernel_support added_block_kernel_block_diagonal

end Formalism.FourierDecayAlt.P

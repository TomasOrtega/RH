import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.NormIndOfSteps
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormInductionOfEstimates
import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.FormalDegreeFormula.CoefPow

namespace CompanionTheory.RgFd

open CompanionTheory.RgDs

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem psiNorm : PsiNorm := psiNorm_of (normInd_of_steps coefPow GlobalTheory.CompanionTheory.RgFdNorm.norm_induction_of_estimates)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem explicit_function_square_integrable : ExplicitFunctionSquareIntegrable := square_integrable_of_norm psiNorm

end CompanionTheory.RgFd

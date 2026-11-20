import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdicCompletionIntegersNormEqOneOfMulEqOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FAdicCompletionIntegersNormEqOneOfMulEqOne.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.norm_eq_one_of_mul_eq_one_adicCompletionIntegers : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletionIntegers F), x * y = 1 → ‖(x : Fv F v)‖ = 1 := by
  first | exact @GlobalTheory.adicCompletionIntegers_norm_eq_one_of_mul_eq_one | exact GlobalTheory.adicCompletionIntegers_norm_eq_one_of_mul_eq_one | (intros; apply GlobalTheory.adicCompletionIntegers_norm_eq_one_of_mul_eq_one <;> assumption)

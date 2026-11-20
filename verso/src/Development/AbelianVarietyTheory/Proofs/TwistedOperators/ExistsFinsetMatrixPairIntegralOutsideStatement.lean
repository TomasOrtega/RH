import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetMatrixPairIntegralOutside
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.matrixPair_integral_cofinite` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsFinsetMatrixPairIntegralOutside.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_finset_matrixPair_integral_outside : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (M N : Matrix κ κ (Af F)), ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, ∀ i j, evalV F v (M i j) ∈ v.adicCompletionIntegers F ∧ evalV F v (N i j) ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.matrixPair_integral_cofinite | exact GlobalTheory.matrixPair_integral_cofinite | (intros; apply GlobalTheory.matrixPair_integral_cofinite <;> assumption)

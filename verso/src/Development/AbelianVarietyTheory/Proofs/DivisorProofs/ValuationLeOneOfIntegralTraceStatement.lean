import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfIntegralTrace
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CodiffValPrimeW.valuation_le_one_of_mem_codiff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FValuationLeOneOfIntegralTrace.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.valuation_le_one_of_integral_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ B.P → ∀ c : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * c))) → w.valuation E c ≤ 1 := by
  first | exact @GlobalTheory.CodiffValPrimeW.valuation_le_one_of_mem_codiff | exact GlobalTheory.CodiffValPrimeW.valuation_le_one_of_mem_codiff | (intros; apply GlobalTheory.CodiffValPrimeW.valuation_le_one_of_mem_codiff <;> assumption)

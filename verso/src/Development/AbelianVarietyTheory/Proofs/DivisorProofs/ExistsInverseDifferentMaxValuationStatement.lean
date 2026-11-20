import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseDifferentMaxValuation
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open NumberField IsDedekindDomain
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.invDifferent_exists_max_valuation` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsInverseDifferentMaxValuation.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_inverseDifferent_max_valuation : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ e : E, e ≠ 0 ∧ (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) ∧ ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) → w.valuation E f ≤ w.valuation E e := by
  first | exact @GlobalTheory.invDifferent_exists_max_valuation | exact GlobalTheory.invDifferent_exists_max_valuation | (intros; apply GlobalTheory.invDifferent_exists_max_valuation <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerDenominatorNotMemOfValuationLeOne
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open NumberField IsDedekindDomain
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IntegralDenom.exists_denom_not_mem` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsIntegerDenominatorNotMemOfValuationLeOne.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_integer_denominator_not_mem_of_valuation_le_one : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : E), w.valuation E a ≤ 1 → ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∃ r : 𝓞 E, (s : E) * a = r := by
  first | exact @GlobalTheory.IntegralDenom.exists_denom_not_mem | exact GlobalTheory.IntegralDenom.exists_denom_not_mem | (intros; apply GlobalTheory.IntegralDenom.exists_denom_not_mem <;> assumption)

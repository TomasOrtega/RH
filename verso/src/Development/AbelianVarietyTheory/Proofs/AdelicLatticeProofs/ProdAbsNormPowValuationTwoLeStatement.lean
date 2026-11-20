import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ProdAbsNormPowValuationTwoLe
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.QNorm.prod_absNorm_pow_le_two_pow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FProdAbsNormPowValuationTwoLe.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.prod_absNorm_pow_valuation_two_le : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (e : HeightOneSpectrum (𝓞 F) → ℕ), (∀ v ∈ S, v.valuation F 2 = WithZero.exp (-(e v : ℤ))) → ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v ≤ 2 ^ Module.finrank ℚ F := by
  first | exact @GlobalTheory.QNorm.prod_absNorm_pow_le_two_pow | exact GlobalTheory.QNorm.prod_absNorm_pow_le_two_pow | (intros; apply GlobalTheory.QNorm.prod_absNorm_pow_le_two_pow <;> assumption)

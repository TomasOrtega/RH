import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoPowCardLeIndexIInf
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FTwoPowCardLeIndexIInf.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.two_pow_card_le_index_iInf_of_independent : ∀ (G ι : Type) [CommGroup G] [Fintype ι] (K : ι → Subgroup G), (∀ i, ∃ x, x ∉ K i ∧ ∀ j, j ≠ i → x ∈ K j) → (⨅ i, K i).index ≠ 0 → 2 ^ Fintype.card ι ≤ (⨅ i, K i).index := by
  first | exact @GlobalTheory.QNorm.two_pow_card_le_index_iInf | exact GlobalTheory.QNorm.two_pow_card_le_index_iInf | (intros; apply GlobalTheory.QNorm.two_pow_card_le_index_iInf <;> assumption)

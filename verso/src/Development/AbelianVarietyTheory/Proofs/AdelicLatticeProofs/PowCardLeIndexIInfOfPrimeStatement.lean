import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowCardLeIndexIInfOfPrime
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FPowCardLeIndexIInfOfPrime.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.pow_card_le_index_iInf_of_prime' : ∀ (p : ℕ) (G ι : Type) [CommGroup G] [Fintype ι] (K : ι → Subgroup G), p.Prime → (∀ (i : ι) (x : G), x ^ p ∈ K i) → (∀ i, ∃ x, x ∉ K i ∧ ∀ j, j ≠ i → x ∈ K j) → (⨅ i, K i).index ≠ 0 → p ^ Fintype.card ι ≤ (⨅ i, K i).index := by
  first | exact @GlobalTheory.CNorm.pow_card_le_index_iInf_of_prime | exact GlobalTheory.CNorm.pow_card_le_index_iInf_of_prime | (intros; apply GlobalTheory.CNorm.pow_card_le_index_iInf_of_prime <;> assumption)

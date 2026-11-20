import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNatCastMemDifferentIdealPowLe
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCuspFormEvaluations%2FExistsNatCastMemDifferentIdealPowLe.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.exists_natCast_mem_differentIdeal_pow_le_discr_sq : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E], ∃ N : ℕ, 0 < N ∧ ((N : ℕ) : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E) ∧ (N : ℝ) ^ Module.finrank ℚ E ≤ |(NumberField.discr E : ℝ)| ^ 2 := by
  first | exact @GlobalTheory.exists_natCast_mem_differentIdeal_pow_le | exact GlobalTheory.exists_natCast_mem_differentIdeal_pow_le | (intros; apply GlobalTheory.exists_natCast_mem_differentIdeal_pow_le <;> assumption)

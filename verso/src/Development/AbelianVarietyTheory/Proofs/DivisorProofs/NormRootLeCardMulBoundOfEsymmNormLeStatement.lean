import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormRootLeCardMulBoundOfEsymmNormLe
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNormRootLeCardMulBoundOfEsymmNormLe.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.norm_root_le_card_mul_bound_of_esymm_norm_le : ∀ (n : ℕ) (B : Multiset ℂˣ) (M : ℝ), B.card = n → 1 ≤ M → (∀ j, 1 ≤ j → j ≤ n → ‖(B.map fun b : ℂˣ => (b : ℂ)).esymm j‖ ≤ M) → ∀ b ∈ B, ‖(b : ℂ)‖ ≤ n * M := by
  first | exact @GlobalTheory.cauchy_roots_bound | exact GlobalTheory.cauchy_roots_bound | (intros; apply GlobalTheory.cauchy_roots_bound <;> assumption)

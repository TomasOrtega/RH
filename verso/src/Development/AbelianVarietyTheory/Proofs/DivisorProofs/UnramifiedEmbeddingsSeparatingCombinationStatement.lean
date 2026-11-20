import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedEmbeddingsSeparatingCombination
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_integral_idempotent_of_not_dvd_discr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnramifiedEmbeddingsSeparatingCombination.lean&line=70#L70)
-/
theorem _root_.GlobalTheory.T.unramified_embeddings_separating_combination : ∀ (E : Type) [Field E] [NumberField E] (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 → ¬ p ∣ (NumberField.discr E).natAbs → ∀ σ : E →+* C, ∃ (n : ℕ) (a : Fin n → 𝓞 E) (c : Fin n → C), (∀ j, ‖c j‖ ≤ 1) ∧ ∑ j, c j * σ (a j : E) = 1 ∧ ∀ φ : E →+* C, φ ≠ σ → ∑ j, c j * φ (a j : E) = 0 := by
  first | exact @GlobalTheory.exists_integral_idempotent_of_not_dvd_discr | exact GlobalTheory.exists_integral_idempotent_of_not_dvd_discr | (intros; apply GlobalTheory.exists_integral_idempotent_of_not_dvd_discr <;> assumption)

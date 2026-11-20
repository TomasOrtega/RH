import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRepresentativesModSimilitudeTranspose

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_representatives_mod_similitude_transpose` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FThetaLawProofs%2FExistsRepresentativesModSimilitudeTranspose.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.exists_perm_representatives_mod_similitude : ∀ (g m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ), 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → ∃ k n : (Fin 4 → Fin (m ^ g)) → Fin 4 → Fin g → ℤ, ∀ k' n' : (Fin 4 → Fin (m ^ g)) → Fin 4 → Fin g → ℤ, (∀ I I', I ≠ I' → ¬ ∃ d e : Fin 4 → Fin g → ℤ, ∀ c, k' I c = k' I' c + ∑ r, al r c • d r ∧ n' I c = n' I' c + ∑ r, al r c • e r) → ∃ σ : Equiv.Perm (Fin 4 → Fin (m ^ g)), ∀ I, ∃ d e : Fin 4 → Fin g → ℤ, ∀ c, k' I c = k (σ I) c + ∑ r, al r c • d r ∧ n' I c = n (σ I) c + ∑ r, al r c • e r := by
  first | exact @GlobalTheory.exists_representatives_mod_similitude_transpose | exact GlobalTheory.exists_representatives_mod_similitude_transpose | (intros; apply GlobalTheory.exists_representatives_mod_similitude_transpose <;> assumption)

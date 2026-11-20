import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNormOneReflectionCorrectionAtLevel
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnRep.exists_refl_correction` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FExistsNormOneReflectionCorrectionAtLevel.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.exists_norm_one_reflection_correction_at_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (x : Fin n → E) (u : E) (N D : ℕ), hermE c G x x ≠ 0 → u * c u = 1 → 0 < N → 0 < D → ∃ u' : E, u' * c u' = 1 ∧ CongAt L N D (refl c G x (u' / u)) ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ ∀ v ∈ L, s • (refl c G x u' *ᵥ v) ∈ L ∧ s • (refl c G x u'⁻¹ *ᵥ v) ∈ L := by
  first | exact @GlobalTheory.UnRep.exists_refl_correction | exact GlobalTheory.UnRep.exists_refl_correction | (intros; apply GlobalTheory.UnRep.exists_refl_correction <;> assumption)

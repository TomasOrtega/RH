import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsResidueClassNearRealEmbeddings
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FExistsResidueClassNearRealEmbeddings.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.exists_residueClass_near_real_embeddings : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (m : Ideal (𝓞 F)) (a₀ : 𝓞 F), m ≠ ⊥ → ∃ C : ℝ, ∀ y : (F →+* ℝ) → ℝ, ∃ a : 𝓞 F, a - a₀ ∈ m ∧ ∀ τ : F →+* ℝ, |τ (a : F) - y τ| ≤ C := by
  first | exact @GlobalTheory.residueClass_relativelyDense | exact GlobalTheory.residueClass_relativelyDense | (intros; apply GlobalTheory.residueClass_relativelyDense <;> assumption)

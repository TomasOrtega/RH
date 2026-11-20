import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalOrthogonalProjectionSemilinear
import Mathlib
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsRationalOrthogonalProjectionSemilinear.lean&line=72#L72)
-/
theorem _root_.GlobalTheory.T.exists_rational_orthogonal_projection_semilinear : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (n : ℕ) (j : (Fin n → K) →ₛₗ[σ] W), (∀ x y, ⟪j x, j y⟫_ℂ ∈ Set.range σ) → ∀ (N : Submodule K (Fin n → K)) (x : Fin n → K), ∃ y ∈ N, j x - j y ∈ (Submodule.span ℂ (j '' (N : Set (Fin n → K))))ᗮ := by
  first | exact @GlobalTheory.exists_mem_sub_mem_orthogonal_span_of_inner_mem_range | exact GlobalTheory.exists_mem_sub_mem_orthogonal_span_of_inner_mem_range | (intros; apply GlobalTheory.exists_mem_sub_mem_orthogonal_span_of_inner_mem_range <;> assumption)

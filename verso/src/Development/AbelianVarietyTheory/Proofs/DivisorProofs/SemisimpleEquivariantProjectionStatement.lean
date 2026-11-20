import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemisimpleEquivariantProjection
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_isotypic_projector` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSemisimpleEquivariantProjection.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.semisimple_equivariant_projection : ∀ (R : Type) [Ring R] (M : Type) [AddCommGroup M] [Module R M], IsSemisimpleModule R M → ∀ x₀ : M, ∃ P : M →ₗ[R] M, P x₀ = x₀ ∧ (∀ v, P (P v) = P v) ∧ (∀ g : M →ₗ[R] M, ∀ v, P (g v) = g (P v)) ∧ ∀ (W : Submodule R M), x₀ ∈ W → ∀ a : R, (∀ u ∈ W, a • u = 0) → ∀ v, a • P v = 0 := by
  first | exact @GlobalTheory.exists_isotypic_projector | exact GlobalTheory.exists_isotypic_projector | (intros; apply GlobalTheory.exists_isotypic_projector <;> assumption)

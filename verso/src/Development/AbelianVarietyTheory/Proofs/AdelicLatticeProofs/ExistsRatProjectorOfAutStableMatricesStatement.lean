import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatProjectorOfAutStableMatrices
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FExistsRatProjectorOfAutStableMatrices.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.exists_rat_projector_of_autStable_matrices : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (E : Submodule ℂ (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ x ∈ E, x.map σ ∈ E) → ∃ c : ι × ι → ι × ι → ℚ, (∀ X : Matrix ι ι ℂ, linExt c X ∈ E) ∧ ∀ x ∈ E, linExt c x = x := by
  first | exact @GlobalTheory.ClassFin.RatProj.exists_rat_projector | exact GlobalTheory.ClassFin.RatProj.exists_rat_projector | (intros; apply GlobalTheory.ClassFin.RatProj.exists_rat_projector <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMatrixProjectionSelfDualLattices
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsMatrixProjectionSelfDualLattices.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.exists_matrix_projection_selfDual_lattices : ∀ (D : D7) (n : ℕ) (L₁ L₃ : Lat D n), SD D L₁ → SD D L₃ → ∃ π : Matrix (Fin n) (Fin n) D.host.E, (∀ v ∈ L₁ ⊔ L₃, π.mulVec v ∈ L₁) ∧ (∀ v ∈ L₃, π.mulVec v ∈ L₃) ∧ ∀ v ∈ L₁, v - π.mulVec v ∈ L₃ := by
  first | exact @GlobalTheory.LatticeProjection.exists_matrix_projection | exact GlobalTheory.LatticeProjection.exists_matrix_projection | (intros; apply GlobalTheory.LatticeProjection.exists_matrix_projection <;> assumption)

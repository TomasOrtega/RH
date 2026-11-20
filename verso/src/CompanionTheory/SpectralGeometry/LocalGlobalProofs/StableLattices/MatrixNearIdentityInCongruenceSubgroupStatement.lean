import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MatrixNearIdentityInCongruenceSubgroup
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FMatrixNearIdentityInCongruenceSubgroup.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.matrix_near_identity_in_congruence_subgroup : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), r < 1 → ∀ A : Matrix (Fin n) (Fin n) L, (∀ i j, ‖(A - 1) i j‖ ≤ r) → ∃ k ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1, (k : Matrix (Fin n) (Fin n) L) = A := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.exists_mem_congK_of_entries | exact GlobalTheory.CompanionTheory.CartGL.exists_mem_congK_of_entries | (intros; apply GlobalTheory.CompanionTheory.CartGL.exists_mem_congK_of_entries <;> assumption)

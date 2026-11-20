import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteCosetRepresentatives
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsFiniteCosetRepresentatives.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.exists_finite_coset_representatives : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A H : AddSubgroup X), IsCompact (A : Set X) → IsOpen (H : Set X) → H ≤ A → ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H := by
  first | exact @GlobalTheory.CompanionTheory.OpenSubgroupTransversal.main | exact GlobalTheory.CompanionTheory.OpenSubgroupTransversal.main | (intros; apply GlobalTheory.CompanionTheory.OpenSubgroupTransversal.main <;> assumption)

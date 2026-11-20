import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumSublatticeIndexRpowLeSolomon
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SubZeta.sum_index_rpow_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FSumSublatticeIndexRpowLeSolomon.lean&line=301#L301)
-/
theorem _root_.GlobalTheory.T.sum_sublattice_index_rpow_le_solomon : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (r : ℕ) (σ : ℝ), (r : ℝ) - 1 < σ → ∀ C : Finset (Submodule O (Fin r → O)), (∀ M ∈ C, M.toAddSubgroup.index ≠ 0) → ∑ M ∈ C, (M.toAddSubgroup.index : ℝ) ^ (-σ) ≤ ∏ i ∈ Finset.range r, (1 - (Nat.card (IsLocalRing.ResidueField O) : ℝ) ^ ((i : ℝ) - σ))⁻¹ := by
  first | exact @GlobalTheory.SubZeta.sum_index_rpow_le | exact GlobalTheory.SubZeta.sum_index_rpow_le | (intros; apply GlobalTheory.SubZeta.sum_index_rpow_le <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductNeighbourhoodsShrinkCompactOpen
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BigCell.preimage_box_shrinking` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FProductNeighbourhoodsShrinkCompactOpen.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.product_neighbourhoods_shrink_compact_open : ∀ (G A ι : Type) [AddCommGroup G] [TopologicalSpace G] [AddCommGroup A] [TopologicalSpace A] [Finite ι] (e : G ≃ₜ+ (ι → A)) (U : ℕ → Set A), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : A) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : A)).smallSets → (∀ k, IsCompact (e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ IsOpen (e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ (0 : G) ∈ e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ Filter.Tendsto (fun k => e ⁻¹' Set.pi Set.univ (fun _ => U k)) Filter.atTop (nhds (0 : G)).smallSets := by
  first | exact @GlobalTheory.CompanionTheory.BigCell.preimage_box_shrinking | exact GlobalTheory.CompanionTheory.BigCell.preimage_box_shrinking | (intros; apply GlobalTheory.CompanionTheory.BigCell.preimage_box_shrinking <;> assumption)

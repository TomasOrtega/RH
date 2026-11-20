import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DominantPartialSumBounds
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Top.partialSum_sub_mean_bounds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FDominantPartialSumBounds.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.dominant_partial_sum_bounds : ∀ (N j : ℕ) (u : Fin N → ℝ), j ≤ N → 0 < N → (∀ a b : Fin N, a ≤ b → u b ≤ u a) → 0 ≤ (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), u i) - j * ((∑ i, u i) / N) ∧ (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), u i) - j * ((∑ i, u i) / N) ≤ ∑ i, |u i| ∧ |∑ i, u i| ≤ ∑ i, |u i| := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.partialSum_sub_mean_bounds | exact GlobalTheory.CompanionTheory.Ar.Top.partialSum_sub_mean_bounds | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.partialSum_sub_mean_bounds <;> assumption)

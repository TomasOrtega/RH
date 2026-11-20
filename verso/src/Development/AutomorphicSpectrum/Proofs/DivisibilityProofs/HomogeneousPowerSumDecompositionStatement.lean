import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HomogeneousPowerSumDecomposition
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Top.form_top_succ_eq_sum_pk` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FHomogeneousPowerSumDecomposition.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.homogeneous_power_sum_decomposition : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (F : RP Ψ N), 2 ≤ N → F.IsHomogeneous (dimFl Ψ N + 1) → ∃ Q : Ψ → ℕ → RP Ψ N, (∀ τ k, 1 ≤ k → k ≤ N → (Q τ k).IsHomogeneous (dimFl Ψ N + 1 - k)) ∧ F = ∑ τ, ∑ k ∈ Finset.Icc 1 N, pk τ k * Q τ k := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.form_top_succ_eq_sum_pk | exact GlobalTheory.CompanionTheory.Ar.Top.form_top_succ_eq_sum_pk | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.form_top_succ_eq_sum_pk <;> assumption)

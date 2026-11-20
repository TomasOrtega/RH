import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRescaledConvergentSubsequence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LimVec.normalised_subseq_limit` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsRescaledConvergentSubsequence.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_rescaled_convergent_subsequence : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (g : ℕ → M), (∀ k, g k ≠ 0) → ∃ (c : ℕ → ℂ) (φ : ℕ → ℕ) (G : M), StrictMono φ ∧ G ≠ 0 ∧ ∀ ℓ : Module.Dual ℂ M, Tendsto (fun k => c k * ℓ (g (φ k))) atTop (𝓝 (ℓ G)) := by
  first | exact @GlobalTheory.CompanionTheory.LimVec.normalised_subseq_limit | exact GlobalTheory.CompanionTheory.LimVec.normalised_subseq_limit | (intros; apply GlobalTheory.CompanionTheory.LimVec.normalised_subseq_limit <;> assumption)

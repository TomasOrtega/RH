import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorSumAnnihilator
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.KillSum.sum_killed` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTensorSumAnnihilator.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.tensor_sum_annihilator : ∀ {ι : Type} (T : Finset ι) (l : ι → Multiset ℂ), ∃ l' : Multiset ℂ, Multiset.card l' = ∏ τ ∈ T, Multiset.card (l τ) ∧
  ∀ (R : Type) [CommRing R] [Algebra ℂ R] (h : ι → R), (∀ τ ∈ T, ((l τ).map fun c => h τ - algebraMap ℂ R c).prod = 0) →
    (l'.map fun c => ∑ τ ∈ T, h τ - algebraMap ℂ R c).prod = 0 := by
  first | exact @GlobalTheory.CompanionTheory.KillSum.sum_killed | exact GlobalTheory.CompanionTheory.KillSum.sum_killed | (intros; apply GlobalTheory.CompanionTheory.KillSum.sum_killed <;> assumption)

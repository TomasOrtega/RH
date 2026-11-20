import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOfLatticeDecay
import Mathlib
open MeasureTheory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LatticeCount.summable_of_lattice_decay` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSummableOfLatticeDecay.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.summable_of_lattice_decay_of_injective : ∀ (ι : Type) (d : ℕ) (w : ι → ℂ) (f : ι → Fin d → ℝ), Function.Injective f → ∀ (N : ℕ), 0 < N → ∀ (C : ℝ), (∀ i, ‖w i‖ * ∏ k, (1 + f i k ^ 2) ≤ C) → (∀ i, w i ≠ 0 → ∀ k, ∃ n : ℤ, (N : ℝ) * f i k = n) → Summable w := by
  first | exact @GlobalTheory.CompanionTheory.LatticeCount.summable_of_lattice_decay | exact GlobalTheory.CompanionTheory.LatticeCount.summable_of_lattice_decay | (intros; apply GlobalTheory.CompanionTheory.LatticeCount.summable_of_lattice_decay <;> assumption)

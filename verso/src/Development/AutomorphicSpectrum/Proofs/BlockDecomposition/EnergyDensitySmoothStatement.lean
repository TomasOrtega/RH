import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyDensitySmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.WaveSpd.sm_dens_inner` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FEnergyDensitySmooth.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.energy_density_smooth : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] (u : ℝ → Mat n → W), Sm u → Sm (dens u) ∧ ∀ (X : Mat n) (v : ℝ → Mat n → W), Sm v → Sm fun s y => ⟪Rt X u s y, v s y⟫_ℝ := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.sm_dens_inner | exact GlobalTheory.CompanionTheory.WaveSpd.sm_dens_inner | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.sm_dens_inner <;> assumption)

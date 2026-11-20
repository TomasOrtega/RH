import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveTimeAverageIsWave
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.WaveMult.WaveAvg.isWave_avg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWaveTimeAverageIsWave.lean&line=267#L267)
-/
theorem _root_.GlobalTheory.T.wave_time_average_is_wave : WaveSpeed → ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V) (g : ℝ → ℝ) (T : ℝ), IsWave E u → IsBump g T → IsWave E (fun t x => ∫ s, (g s : ℂ) • u (t + s) x) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.WaveAvg.isWave_avg | exact GlobalTheory.CompanionTheory.WaveMult.WaveAvg.isWave_avg | (intros; apply GlobalTheory.CompanionTheory.WaveMult.WaveAvg.isWave_avg <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelComposition
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
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWaveKernelComposition.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.wave_kernel_composition : RCalc → WaveSpeed → ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V) (w w' : List (Bool × ℕ)) (g g' : ℝ → ℝ) (T T' : ℝ), IsWave E u → IsBump g T → IsBump g' T' → ∃ v : ℝ → Mat n → E.V, IsWave E v ∧ (∀ x ∈ GLs n, v 0 x = zOp w' (fun x' => ∫ t, (g' t : ℂ) • u t x') x) ∧ ∀ x ∈ GLs n, zOp w (fun x' => ∫ t, (g t : ℂ) • v t x') x = zOp (w ++ w') (fun x' => ∫ t, (gconv g g' t : ℂ) • u t x') x := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.wave_compose | exact GlobalTheory.CompanionTheory.WaveMult.wave_compose | (intros; apply GlobalTheory.CompanionTheory.WaveMult.wave_compose <;> assumption)

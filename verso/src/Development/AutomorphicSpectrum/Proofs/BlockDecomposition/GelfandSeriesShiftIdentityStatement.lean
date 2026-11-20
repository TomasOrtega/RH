import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandSeriesShiftIdentity
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

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGelfandSeriesShiftIdentity.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.gelfand_series_shift_identity : ∀ (n : ℕ) (c : Fin n → ℂ), (1 - PowerSeries.X * gser c) * ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2) * PowerSeries.X) = ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2 + 1) * PowerSeries.X) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.gser_mul_prod | exact GlobalTheory.CompanionTheory.WaveMult.gser_mul_prod | (intros; apply GlobalTheory.CompanionTheory.WaveMult.gser_mul_prod <;> assumption)

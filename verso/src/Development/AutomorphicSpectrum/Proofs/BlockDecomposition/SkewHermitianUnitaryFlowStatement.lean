import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SkewHermitianUnitaryFlow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSkewHermitianUnitaryFlow.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.skew_hermitian_unitary_flow : ∀ {n : ℕ} (Y : Mat n), Yᴴ = -Y → ∃ c : ℝ → Matrix.unitaryGroup (Fin n) ℂ, Continuous c ∧ c 0 = 1 ∧ (∀ s t, c (s + t) = c s * c t) ∧ HasDerivAt (fun t => (c t).1) Y 0 := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.UnitaryCurve.exists_unitary_curve | exact GlobalTheory.CompanionTheory.WaveSpd.UnitaryCurve.exists_unitary_curve | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.UnitaryCurve.exists_unitary_curve <;> assumption)

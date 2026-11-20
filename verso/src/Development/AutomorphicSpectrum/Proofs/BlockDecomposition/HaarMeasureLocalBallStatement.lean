import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureLocalBall
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetOff
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Equi.BallVol.measure_translate_ballV` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHaarMeasureLocalBall.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.haar_measure_local_ball : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (k : ℕ) (a : Fv F v), lam ((fun z => z - a) ⁻¹' ballV v k) = ENNReal.ofReal (((Ideal.absNorm v.asIdeal : ℝ) ^ k)⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.Equi.BallVol.measure_translate_ballV | exact GlobalTheory.CompanionTheory.Equi.BallVol.measure_translate_ballV | (intros; apply GlobalTheory.CompanionTheory.Equi.BallVol.measure_translate_ballV <;> assumption)

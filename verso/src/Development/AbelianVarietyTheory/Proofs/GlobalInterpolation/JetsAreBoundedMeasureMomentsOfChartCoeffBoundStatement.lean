import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetsAreBoundedMeasureMomentsOfChartCoeffBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MomOneAmice.momInt_of_bd_hat` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FJetsAreBoundedMeasureMomentsOfChartCoeffBound.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.jetsAreBoundedMeasureMoments_of_chart_coeff_bound : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ), Differentiable ℂ G → Bd 1 (hat ι (C ω * logS) G) → MomInt ι (fun _ : Unit => ι.symm ω) G := by
  first | exact @GlobalTheory.MomOneAmice.momInt_of_bd_hat | exact GlobalTheory.MomOneAmice.momInt_of_bd_hat | (intros; apply GlobalTheory.MomOneAmice.momInt_of_bd_hat <;> assumption)

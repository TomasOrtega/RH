import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedWeierstrassCurveTransformCoefficientsW
import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FUnramifiedWeierstrassCurveTransformCoefficientsW.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.unramifiedWeierstrassCurve_transform_coefficients_wellFormed : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]), W.a₁ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₂ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₃ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₄ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₆ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → ∀ s2 : ℂ_[p], s2 ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → Formalism.MainNotions.GL3Theta.CoefWf (Formalism.L2.Th1.B.phW W s2 : MvPowerSeries Unit ℂ_[p]) := by
  first | exact @GlobalTheory.CoefWfUnram.coefWf_phW | exact GlobalTheory.CoefWfUnram.coefWf_phW | (intros; apply GlobalTheory.CoefWfUnram.coefWf_phW <;> assumption)

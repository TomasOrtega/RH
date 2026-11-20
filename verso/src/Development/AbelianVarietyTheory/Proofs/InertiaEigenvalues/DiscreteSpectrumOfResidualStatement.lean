import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DiscreteSpectrumResidual
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SpehInfChar.discreteSpectrumGL_of_residual` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FDiscreteSpectrumOfResidual.lean&line=281#L281)
-/
theorem _root_.GlobalTheory.T.discrete_spectrum_of_residual : GlobalTheory.Published.DiscreteSpectrumResidual → GlobalTheory.Published.DiscreteSpectrumGL := by
  first | exact @GlobalTheory.SpehInfChar.discreteSpectrumGL_of_residual | exact GlobalTheory.SpehInfChar.discreteSpectrumGL_of_residual | (intros; apply GlobalTheory.SpehInfChar.discreteSpectrumGL_of_residual <;> assumption)

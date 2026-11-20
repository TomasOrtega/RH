import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiCentreEigenfunctionDiscreteSeries
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FPhiCentreEigenfunctionDiscreteSeries.lean&line=413#L413)
-/
theorem _root_.GlobalTheory.T.phi_centre_eigenfunction_discrete_series : PhiEigen := by
  first | exact @GlobalTheory.PhiEigenfun.phiEigen | exact GlobalTheory.PhiEigenfun.phiEigen | (intros; apply GlobalTheory.PhiEigenfun.phiEigen <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BlowUpFibreSemilocal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegreeCut
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FBlowUpFibreSemilocal.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.blow_up_fibre_semilocal : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpFibreSemilocal.Statement.{0} := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.BlowUpFibre.main | exact GlobalTheory.CompanionTheory.CommAlg.BlowUpFibre.main | (intros; apply GlobalTheory.CompanionTheory.CommAlg.BlowUpFibre.main <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CommAlg.FlagIndependence.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FFlagIndependence.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.flag_independence : GroundTheory.Heights₂.Heights.NumbersDVR.FlagIndependence.Statement := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.FlagIndependence.main | exact GlobalTheory.CompanionTheory.CommAlg.FlagIndependence.main | (intros; apply GlobalTheory.CompanionTheory.CommAlg.FlagIndependence.main <;> assumption)

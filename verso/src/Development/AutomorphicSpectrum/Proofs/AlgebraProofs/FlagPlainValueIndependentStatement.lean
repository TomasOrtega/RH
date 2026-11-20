import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagPlainValueIndependent
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerAlt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CommAlg.FlagPlainValue.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FFlagPlainValueIndependent.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.flag_plain_value_independent : GroundTheory.Heights₂.Heights.NumbersDVR.FlagPlainValueIndependence.Statement := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.FlagPlainValue.main | exact GlobalTheory.CompanionTheory.CommAlg.FlagPlainValue.main | (intros; apply GlobalTheory.CompanionTheory.CommAlg.FlagPlainValue.main <;> assumption)

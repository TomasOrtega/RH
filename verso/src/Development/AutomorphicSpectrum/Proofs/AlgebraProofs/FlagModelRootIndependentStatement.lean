import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelRootIndependent
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitAlt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.RootIndep.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FFlagModelRootIndependent.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.flag_model_root_independent : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelRootIndependence.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootIndep.main | exact GlobalTheory.CompanionTheory.Ar.RootIndep.main | (intros; apply GlobalTheory.CompanionTheory.Ar.RootIndep.main <;> assumption)

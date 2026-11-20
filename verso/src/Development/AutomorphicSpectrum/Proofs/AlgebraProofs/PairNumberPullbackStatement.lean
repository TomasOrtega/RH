import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PairNumberPullback
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Num.PairNumberPullback.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FPairNumberPullback.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.pair_number_pullback : GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberPullback.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.PairNumberPullback.main | exact GlobalTheory.CompanionTheory.Ar.Num.PairNumberPullback.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.PairNumberPullback.main <;> assumption)

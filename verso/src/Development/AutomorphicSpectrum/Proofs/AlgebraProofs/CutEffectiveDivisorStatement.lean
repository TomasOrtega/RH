import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CutEffectiveDivisor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.Ar.Num.CutClosed.main | exact GlobalTheory.CompanionTheory.Ar.Num.CutClosed.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.CutClosed.main <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.cut_effective_divisor : GroundTheory.Heights₂.Heights.NumbersDVR.CutByEffectiveDivisor.Statement.{0} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.CutClosed.main | exact GlobalTheory.CompanionTheory.Ar.Num.CutClosed.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.CutClosed.main <;> assumption)

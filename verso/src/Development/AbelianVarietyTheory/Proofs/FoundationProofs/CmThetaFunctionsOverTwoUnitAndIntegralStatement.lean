import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaFunctionsOverTwoUnitAndIntegral
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.EvenTheta.atTwo | exact GlobalTheory.EvenTheta.atTwo | (intros; apply GlobalTheory.EvenTheta.atTwo <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.cm_theta_functions_over_two_unit_and_integral : ∀ D : D7, GL3Theta.atTwo D := by
  first | exact @GlobalTheory.EvenTheta.atTwo | exact GlobalTheory.EvenTheta.atTwo | (intros; apply GlobalTheory.EvenTheta.atTwo <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaValuesVanishAtOddSplitPrime
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FCmThetaValuesVanishAtOddSplitPrime.lean&line=155#L155)
-/
theorem _root_.GlobalTheory.T.cm_theta_values_vanish_at_odd_split_prime : ∀ D : D7, GL3Theta.splitZero D := by
  first | exact @GlobalTheory.ThetaSplit.splitZero | exact GlobalTheory.ThetaSplit.splitZero | (intros; apply GlobalTheory.ThetaSplit.splitZero <;> assumption)

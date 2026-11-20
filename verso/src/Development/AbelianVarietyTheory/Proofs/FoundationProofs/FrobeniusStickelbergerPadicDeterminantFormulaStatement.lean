import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerPadicDeterminantFormula
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FrobStick.frobenius_stickelberger_padic_determinant_formula` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FFrobeniusStickelbergerPadicDeterminantFormula.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.pAdicFrobeniusStickelberger_of_d7_datum : ∀ D : D7, Formalism.MainNotions.Ext.CutA.PAdicFrobeniusStickelberger D := by
  first | exact @GlobalTheory.FrobStick.frobenius_stickelberger_padic_determinant_formula | exact GlobalTheory.FrobStick.frobenius_stickelberger_padic_determinant_formula | (intros; apply GlobalTheory.FrobStick.frobenius_stickelberger_padic_determinant_formula <;> assumption)

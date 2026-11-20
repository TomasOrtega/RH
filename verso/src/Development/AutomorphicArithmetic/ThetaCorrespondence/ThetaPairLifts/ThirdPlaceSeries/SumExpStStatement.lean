import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumExpansionStatementStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModelStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SumExpStAltAlt

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FSumExpStAltAlt.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.sum_expansion' : _root_.GlobalTheory.ExpTie.ExponentSumStatement := by
  first | exact @_root_.GlobalTheory.ExpTie.sumExpSt_alt | exact _root_.GlobalTheory.ExpTie.sumExpSt_alt | (intros; apply _root_.GlobalTheory.ExpTie.sumExpSt_alt <;> assumption)
end

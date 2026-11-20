import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelRationalityAtPlaceStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadComparisonAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KerOfAt

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FKerOfAt.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.kerOfAt' : _root_.GlobalTheory.BigOn.Exp.SerBase.KerOfAtAlt := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.SerBase.kerOfAt_alt | exact _root_.GlobalTheory.BigOn.Exp.SerBase.kerOfAt_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.SerBase.kerOfAt_alt <;> assumption)
end

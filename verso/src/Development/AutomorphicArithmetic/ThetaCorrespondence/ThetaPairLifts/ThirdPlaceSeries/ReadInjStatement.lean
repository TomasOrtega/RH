import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadInjectiveStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticeHasSmallGenerators
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadInj

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigOn.Exp.readInj_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FReadInj.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.read_injective : _root_.GlobalTheory.BigOn.Exp.ReadInjAlt := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.readInj_alt | exact _root_.GlobalTheory.BigOn.Exp.readInj_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.readInj_alt <;> assumption)
end

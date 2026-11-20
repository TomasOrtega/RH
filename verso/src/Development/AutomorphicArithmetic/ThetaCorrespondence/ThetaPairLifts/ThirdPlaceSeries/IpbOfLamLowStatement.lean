import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaLowGivesFirstIdentityStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IpbOfLamLow

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigTop.Fun.ipb_of_lamLow_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FIpbOfLamLow.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.leafInfinitePlaceBound_of_lamLow : _root_.GlobalTheory.BigTop.LambdaLowerBound₂ → _root_.GlobalTheory.BigTop.Fun.LeafInfinitePlaceBound := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.ipb_of_lamLow_alt | exact _root_.GlobalTheory.BigTop.Fun.ipb_of_lamLow_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.ipb_of_lamLow_alt <;> assumption)
end

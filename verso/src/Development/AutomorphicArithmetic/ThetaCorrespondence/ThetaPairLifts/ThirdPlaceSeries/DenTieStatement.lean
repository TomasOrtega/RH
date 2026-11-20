import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenominatorFittedIdentityStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DenTie

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigTop.Fun.den_tie_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FDenTie.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.leafDensity_of_logDeriv_bound_and_denSum : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → DenSum → _root_.GlobalTheory.BigTop.Fun.LeafDensity @Comparison₂ := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.den_tie_alt | exact _root_.GlobalTheory.BigTop.Fun.den_tie_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.den_tie_alt <;> assumption)
end

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFamilyEstimateStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThmAUpper

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThmAUpper.thmA_upper_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FThmAUpper.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.toric_ratio_family_estimate' : GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → FieldDat → TorEx → (_root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted @Comparison₂) fun p _ d _ _ => ThA d.G p.P.A3.A.μ0 p.R.mu) := by
  first | exact @_root_.GlobalTheory.ThmAUpper.thmA_upper_alt | exact _root_.GlobalTheory.ThmAUpper.thmA_upper_alt | (intros; apply _root_.GlobalTheory.ThmAUpper.thmA_upper_alt <;> assumption)
end

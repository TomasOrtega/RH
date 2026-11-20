import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthUnitSizeBoundsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Sizes

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FSizes.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.lenT_zBase_unitE_nCol_bounds : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP _ => (lenT p i PP : ℝ) * zBase (Fm.L x ι) ^ 12 ≤ unitE p ∧ 1 ≤ (Fm.L x ι).sc.L ∧ lrd (Fm.D x ι).host.E ≤ 3 * (Fm.L x ι).sc.L ∧ (nCol (dat p i) : ℝ) ≤ 20 * (Fm.D x ι).R.f * (Fm.D x ι).R.r ^ 2 ∧ 1 ≤ (Fm.D x ι).R.f ∧ 1 ≤ (Fm.D x ι).R.r := by
  first | exact @_root_.GlobalTheory.RefSum.SizeTZ.parameters_scale_rank_gap_bounds | exact _root_.GlobalTheory.RefSum.SizeTZ.parameters_scale_rank_gap_bounds | (intros; apply _root_.GlobalTheory.RefSum.SizeTZ.parameters_scale_rank_gap_bounds <;> assumption)
end

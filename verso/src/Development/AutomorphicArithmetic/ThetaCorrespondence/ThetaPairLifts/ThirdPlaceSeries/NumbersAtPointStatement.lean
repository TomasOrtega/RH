import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetNumberQuotientBoundsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumbersAtPoint

set_option synthInstance.maxHeartbeats 200000

section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RefSum.NumPtAlt.numbers_at_point` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FNumbersAtPoint.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.jetNum_nCol_lenT_bounds_of_quo : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 → JetNum (Fm.D x ι) (DF (dat p i) (aOf p i u1)) (1 / 2500) ∧ 2 * (Fm.D x ι).R.r ≤ nCol (dat p i) ∧ (lenT p i PP : ℝ) * (Real.log ((Fm.D x ι).host.g 0) + Real.log ((Fm.D x ι).host.g 1)) ≤ C * unitE p := by
  first | exact @_root_.GlobalTheory.RefSum.NumPtAlt.numbers_at_point | exact _root_.GlobalTheory.RefSum.NumPtAlt.numbers_at_point | (intros; apply _root_.GlobalTheory.RefSum.NumPtAlt.numbers_at_point <;> assumption)
end

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLengthLowerBoundQuotientStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DividedWeight

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FDividedWeight.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.torus_length_lower_bound_quotient' : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → zBase (Fm.L x ι) ^ 24 ≤ lenT p i PP ∧ ∀ u1, Quo p i PP u1 → lenT p i PP * GlobalTheory.CovHt.l1 u1 ≤ C * unitE p ∧ ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 → (lenT p i PP : ℤ) ≤ u1 τ a - u1 τ b := by
  first | exact @_root_.GlobalTheory.CovHt.DividedNum.lenT_bounds_of_covers_before_last | exact _root_.GlobalTheory.CovHt.DividedNum.lenT_bounds_of_covers_before_last | (intros; apply _root_.GlobalTheory.CovHt.DividedNum.lenT_bounds_of_covers_before_last <;> assumption)
end

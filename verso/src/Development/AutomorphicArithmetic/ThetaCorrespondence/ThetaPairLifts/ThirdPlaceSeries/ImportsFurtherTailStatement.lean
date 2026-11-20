import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConclusionOfFamilyFactsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherTail

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NLinkClose.main_alt_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FImportsFurtherTail.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.conclF_of_family_facts_and_bound_at_two_three : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∀ (C : ℝ) (CT : ℕ), 0 ≤ C → TwGood Fm → _root_.GlobalTheory.NLink.FactsFAlt Fm C CT → _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm → ConclF Fm := by
  first | exact @_root_.GlobalTheory.NLinkClose.main_alt_alt | exact _root_.GlobalTheory.NLinkClose.main_alt_alt | (intros; apply _root_.GlobalTheory.NLinkClose.main_alt_alt <;> assumption)
end

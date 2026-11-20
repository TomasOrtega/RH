import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHubDataFamilyStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSetupLarge

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NLink.exists_setup_large_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FExistsSetupLarge.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.exists_hubData_admJ_setup : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∀ (C C₂ : ℝ) (CT : ℕ), TwGood Fm → _root_.GlobalTheory.NLink.FactsFAlt Fm C CT → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), TwistedPlaces.ShaFinOdd (Fm.D x i) → ∀ exc : Finset ℕ, ∃ (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW) (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)), X.exc = exc ∧ _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt (Fm.L x i) ∧ _root_.GlobalTheory.NLink.SetupAlt (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ := by
  first | exact @_root_.GlobalTheory.NLink.exists_setup_large_alt | exact _root_.GlobalTheory.NLink.exists_setup_large_alt | (intros; apply _root_.GlobalTheory.NLink.exists_setup_large_alt <;> assumption)
end

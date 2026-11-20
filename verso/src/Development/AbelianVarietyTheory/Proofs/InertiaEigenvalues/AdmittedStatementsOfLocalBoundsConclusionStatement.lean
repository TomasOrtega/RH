import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmittedStatementsOfLocalBoundsConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NLink.admittedStatements_of_localBoundsConclusion` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FAdmittedStatementsOfLocalBoundsConclusion.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.admittedStatements_of_localBoundsConclusion_alt : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ), Concl L P X C → ∃ tb : TwistedPlaces.Tab L, TwistedPlaces.AdmT L tb C P := by
  first | exact @GlobalTheory.NLink.admittedStatements_of_localBoundsConclusion | exact GlobalTheory.NLink.admittedStatements_of_localBoundsConclusion | (intros; apply GlobalTheory.NLink.admittedStatements_of_localBoundsConclusion <;> assumption)

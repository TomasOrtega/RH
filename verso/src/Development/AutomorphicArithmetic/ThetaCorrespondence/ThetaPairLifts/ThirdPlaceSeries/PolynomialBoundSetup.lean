import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolynomialBoundSetupStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainOfAltAlt

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TheoremBQD.main_alt_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FMainOfAltAlt.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.embedding_jumps_aux2_of_setup : ∃ (constantFirstHub : ℝ) (Q : MvPolynomial (Fin 3) ℕ), Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → EmbeddingTypeJumps.Conclusion2 X.ρ L constantFirstHub Q := by
  first | exact @_root_.GlobalTheory.TheoremBQD.main_alt_alt | exact _root_.GlobalTheory.TheoremBQD.main_alt_alt | (intros; apply _root_.GlobalTheory.TheoremBQD.main_alt_alt <;> assumption)
end

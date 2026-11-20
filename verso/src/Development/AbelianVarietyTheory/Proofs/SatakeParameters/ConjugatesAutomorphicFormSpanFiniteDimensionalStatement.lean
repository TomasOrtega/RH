import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugatesAutomorphicFormSpanFiniteDimensional
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ConjSpan.conj_span_finite` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FConjugatesAutomorphicFormSpanFiniteDimensional.lean&line=116#L116)
-/
theorem _root_.GlobalTheory.T.conjugates_automorphicForm_span_finiteDimensional : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (φ : UA E n → ℂ), IsAutFormU φ → ∃ M : Submodule ℂ (UA E n → ℂ), FiniteDimensional ℂ M ∧ ∀ (σ : ℂ ≃+* ℂ) (φ' : UA E n → ℂ), IsAutFormU φ' → (∀ g ∈ finU E n, φ' g = σ (φ g)) → φ' ∈ M := by
  first | exact @GlobalTheory.ConjSpan.conj_span_finite | exact GlobalTheory.ConjSpan.conj_span_finite | (intros; apply GlobalTheory.ConjSpan.conj_span_finite; all_goals assumption)

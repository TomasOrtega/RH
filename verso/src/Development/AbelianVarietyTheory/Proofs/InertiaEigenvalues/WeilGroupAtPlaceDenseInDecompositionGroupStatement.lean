import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupAtPlaceDenseInDecompositionGroup
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.WeilDeligne.exists_weil_apply_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWeilGroupAtPlaceDenseInDecompositionGroup.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.weilGroupAtPlace_dense_in_decompositionGroup : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∀ d ∈ Dec (F := E) A, ∀ y : Ω, ∃ τ ∈ Weil h, τ y = d y := by
  first | exact @GlobalTheory.WeilDeligne.exists_weil_apply_eq | exact GlobalTheory.WeilDeligne.exists_weil_apply_eq | (intros; apply GlobalTheory.WeilDeligne.exists_weil_apply_eq <;> assumption)

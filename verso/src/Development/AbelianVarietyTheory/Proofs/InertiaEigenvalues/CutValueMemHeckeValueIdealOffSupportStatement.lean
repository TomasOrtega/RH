import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutValueMemHeckeValueIdealOffSupport
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Cut.value_mem_ccOff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCutValueMemHeckeValueIdealOffSupport.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.cutValue_mem_heckeValueIdealOffSupport : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ f ∈ S.T', (∀ x', S.p x' ∈ Xs → S.p x' ∉ D.nd.Z i → f x' = 0) → f S.π' ∈ ccOff i Xs π := by
  first | exact @GlobalTheory.Cut.value_mem_ccOff | exact GlobalTheory.Cut.value_mem_ccOff | (intros; apply GlobalTheory.Cut.value_mem_ccOff <;> assumption)

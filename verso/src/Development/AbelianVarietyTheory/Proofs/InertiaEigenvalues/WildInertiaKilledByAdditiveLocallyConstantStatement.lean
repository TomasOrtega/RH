import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildInertiaKilledByAdditiveLocallyConstant
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWildInertiaKilledByAdditiveLocallyConstant.lean&line=149#L149)
-/
theorem _root_.GlobalTheory.T.wildInertia_killed_by_additive_locallyConstant : ∀ (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)), v ∉ placesOver D.host.E (D.nd.l i) → ∀ f : GE D.nd → KOG (D.nd.O i) 1, IsLocallyConstant f → (∀ a ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), ∀ b ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), f (a * b) = f a + f b) → ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 v), f σ = 0 := by
  first | exact @GlobalTheory.WildAdditive.main | exact GlobalTheory.WildAdditive.main | (intros; apply GlobalTheory.WildAdditive.main <;> assumption)

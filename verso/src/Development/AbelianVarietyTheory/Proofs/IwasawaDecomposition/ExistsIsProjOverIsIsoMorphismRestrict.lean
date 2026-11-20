import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsProjOverFiniteFibreProduct
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfIsSchemeTheoreticallyDominantOfFractionRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemBasicOpenOfMemClosure
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ChowLemma

/- English proof (translation)
Establish `hr : Set.range t ⊆ Set.range (π ⁻¹ᵁ W).ι`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Express the relevant statement in the definitionally equal form `π (t x) ∈ W`. Rewrite using `[← Scheme.Hom.comp_apply, ht]`.

Conclude with `h x.2`. Establish `e` using `IsOpenImmersion.lift_fac (π ⁻¹ᵁ W).ι t hr`. Use `⟨IsOpenImmersion.lift (π ⁻¹ᵁ W).ι t hr, ?_, e, ?_⟩` and prove the remaining obligations. Establish `: IsDominant (IsOpenImmersion.lift (π ⁻¹ᵁ W).ι t hr ≫ (π ⁻¹ᵁ W).ι)`. Rewrite using `[e]` and apply the resulting hypothesis.

Conclude with `IsDominant.of_comp_of_isOpenImmersion _ (π ⁻¹ᵁ W).ι`. Rewrite using `[← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, reassoc_of% e, ht, X.homOfLE_ι]`.
-/
theorem exists_dominant_lift {X X' : Scheme.{0}} (π : X' ⟶ X) {U W : X.Opens} (h : U ≤ W)
    (t : U.toScheme ⟶ X') [IsDominant t] (ht : t ≫ π = U.ι) :
    ∃ σ : U.toScheme ⟶ (π ⁻¹ᵁ W).toScheme, IsDominant σ ∧ σ ≫ (π ⁻¹ᵁ W).ι = t ∧
      σ ≫ π ∣_ W = X.homOfLE h := by
  have hr : Set.range t ⊆ Set.range (π ⁻¹ᵁ W).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change π (t x) ∈ W
    rw [← Scheme.Hom.comp_apply, ht]
    exact h x.2
  have e := IsOpenImmersion.lift_fac (π ⁻¹ᵁ W).ι t hr
  refine ⟨IsOpenImmersion.lift (π ⁻¹ᵁ W).ι t hr, ?_, e, ?_⟩
  · have : IsDominant (IsOpenImmersion.lift (π ⁻¹ᵁ W).ι t hr ≫ (π ⁻¹ᵁ W).ι) := by
      rwa [e]
    exact IsDominant.of_comp_of_isOpenImmersion _ (π ⁻¹ᵁ W).ι
  · rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, reassoc_of% e, ht, X.homOfLE_ι]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.BasicOpenLocalExtension.chow_integral`. Consider the case `exact _root_.GlobalTheory.BasicOpenLocalExtension.chow_integral`. Consider the case `(apply _root_.GlobalTheory.BasicOpenLocalExtension.chow_integral <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.BasicOpenLocalExtension.chow_integral <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.BasicOpenLocalExtension.chow_integral <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.BasicOpenLocalExtension.chow_integral ..)`.
-/
theorem exists_isProjOver_isIso_morphismRestrict : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp R) [IsProper f], ∃ (X' : Scheme.{0}) (π : X' ⟶ X) (U : X.Opens), IsProjOver (π ≫ f) ∧ (U : Set X).Nonempty ∧ IsIso (π ∣_ U) := by
  first
  | exact @_root_.GlobalTheory.BasicOpenLocalExtension.chow_integral
  | exact _root_.GlobalTheory.BasicOpenLocalExtension.chow_integral
  | (apply _root_.GlobalTheory.BasicOpenLocalExtension.chow_integral <;> assumption)
  | (intros; apply _root_.GlobalTheory.BasicOpenLocalExtension.chow_integral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.BasicOpenLocalExtension.chow_integral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.BasicOpenLocalExtension.chow_integral ..)

end GlobalTheory.ChowLemma

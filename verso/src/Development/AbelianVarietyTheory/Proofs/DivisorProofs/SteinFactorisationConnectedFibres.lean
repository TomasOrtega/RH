import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiConnectednessIsPreconnectedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SteinFact

/- English proof (translation)
Use `letI := GlobalTheory.algebraΓOfHom f`. Establish `h0` using `GlobalTheory.ProperFinite.finite_coh_of_isProper f (GlobalTheory.structureModule X) 0`. Establish `h1` using `Module.Finite.equiv (GlobalTheory.cohOn.zeroEquiv R (GlobalTheory.structureModule X) ⊤)`. Set `ρ : GlobalTheory.sectionsOn (GlobalTheory.structureModule X) ⊤ →ₗ[R] Γ(X, ⊤)` to `{ toFun := fun s => (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) ⊤ s : Γ(X, ⊤)) map_add' := fun s t => map_add (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) ⊤) s t map_smul' := fun r s => by`. Rewrite using `[GlobalTheory.sectionsOn.toΓ_smul]`.

Rewrite using `[GlobalTheory.restrictGlobal_top]`. Use `rfl }`. Establish `hρ : Function.Bijective ρ` using `(GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) ⊤).bijective`. Conclude with `Module.Finite.equiv (LinearEquiv.ofBijective ρ hρ)`.
-/
theorem finite_appTop_of_isProper {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}}
    (f : X ⟶ Sp R) [IsProper f] :
    ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom.Finite := by
  letI := GlobalTheory.algebraΓOfHom f
  have h0 := GlobalTheory.ProperFinite.finite_coh_of_isProper f (GlobalTheory.structureModule X) 0
  have h1 := Module.Finite.equiv (GlobalTheory.cohOn.zeroEquiv R (GlobalTheory.structureModule X) ⊤)
  let ρ : GlobalTheory.sectionsOn (GlobalTheory.structureModule X) ⊤ →ₗ[R] Γ(X, ⊤) :=
    { toFun := fun s => (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) ⊤ s : Γ(X, ⊤))
      map_add' := fun s t => map_add (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) ⊤) s t
      map_smul' := fun r s => by
        rw [GlobalTheory.sectionsOn.toΓ_smul]
        rw [GlobalTheory.restrictGlobal_top]
        rfl }
  have hρ : Function.Bijective ρ := (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) ⊤).bijective
  exact Module.Finite.equiv (LinearEquiv.ofBijective ρ hρ)

/- English proof (translation)
Set `j` to `(g ⁻¹ᵁ V).ι`. Set `g' : (g ⁻¹ᵁ V).toScheme ⟶ Sp Γ(Y, V)` to `g ∣_ V ≫ hV.isoSpec.hom`. Establish `: IsProper g'` using `inferInstanceAs (IsProper (g ∣_ V ≫ hV.isoSpec.hom))`. Establish `h1` using `finite_appTop_of_isProper g'`. Establish `hle : j ''ᵁ ⊤ ≤ g ⁻¹ᵁ V` using `(g ⁻¹ᵁ V).ι_image_top.le`.

Establish `e : (Scheme.ΓSpecIso (.of Γ(Y, V))).inv ≫ g'.appTop = g.appLE V (j ''ᵁ ⊤) hle`. Use extensionality with `r`. Express the relevant statement in the definitionally equal form `(g ∣_ V ≫ hV.isoSpec.hom).appTop ((Scheme.ΓSpecIso Γ(Y, V)).inv r) = _`. Rewrite using `[Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop, ← CommRingCat.comp_apply, Category.assoc, Iso.inv_hom_id_assoc, GlobalTheory.ProperFinite.topIso_inv_appTop]`. Rewrite `h1` using `[e]`.

Establish `hi : IsIso (X.presheaf.map (homOfLE hle).op)`. Rewrite using `[show homOfLE hle = eqToHom (g ⁻¹ᵁ V).ι_image_top from Subsingleton.elim _ _]`. Use `infer_instance`. Conclude with `(RingHom.finite_respectsIso.cancel_right_isIso _ (X.presheaf.map (homOfLE hle).op)).1 h1`.
-/
theorem finite_app_of_isProper {X Y : Scheme.{0}} (g : X ⟶ Y) [IsProper g] {V : Y.Opens}
    (hV : IsAffineOpen V) [IsNoetherianRing Γ(Y, V)] : (g.app V).hom.Finite := by
  let j := (g ⁻¹ᵁ V).ι
  let g' : (g ⁻¹ᵁ V).toScheme ⟶ Sp Γ(Y, V) := g ∣_ V ≫ hV.isoSpec.hom
  have : IsProper g' := inferInstanceAs (IsProper (g ∣_ V ≫ hV.isoSpec.hom))
  have h1 := finite_appTop_of_isProper g'
  have hle : j ''ᵁ ⊤ ≤ g ⁻¹ᵁ V := (g ⁻¹ᵁ V).ι_image_top.le
  have e : (Scheme.ΓSpecIso (.of Γ(Y, V))).inv ≫ g'.appTop = g.appLE V (j ''ᵁ ⊤) hle := by
    ext r
    change (g ∣_ V ≫ hV.isoSpec.hom).appTop ((Scheme.ΓSpecIso Γ(Y, V)).inv r) = _
    rw [Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop, ← CommRingCat.comp_apply, Category.assoc,
      Iso.inv_hom_id_assoc, GlobalTheory.ProperFinite.topIso_inv_appTop]
  rw [e] at h1
  have hi : IsIso (X.presheaf.map (homOfLE hle).op) := by
    rw [show homOfLE hle = eqToHom (g ⁻¹ᵁ V).ι_image_top from Subsingleton.elim _ _]
    infer_instance
  exact (RingHom.finite_respectsIso.cancel_right_isIso _ (X.presheaf.map (homOfLE hle).op)).1 h1

/- English proof (translation)
Introduce `X Y g hY hg`. Establish `hb : IsFinite g.fromNormalization`. Use `{ toIsAffineHom := inferInstance, finite_app := fun U hU => ?_ }` and prove the remaining obligations. Establish `: IsNoetherianRing Γ(Y, U)` using `IsLocallyNoetherian.component_noetherian ⟨U, hU⟩`. Use `letI := (g.app U).hom.toAlgebra`.

Establish `: Module.Finite Γ(Y, U) Γ(X, g ⁻¹ᵁ U)` using `finite_app_of_isProper g hU`. Establish `: Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, g ⁻¹ᵁ U))` using `Module.IsNoetherian.finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, g ⁻¹ᵁ U)).toSubmodule`. Rewrite using `[g.fromNormalization_app hU]`. Conclude with `(RingHom.finite_respectsIso.cancel_right_isIso _ _).2 (RingHom.finite_algebraMap.2 this)`. Establish `hY' : IsLocallyNoetherian g.normalization` using `LocallyOfFiniteType.isLocallyNoetherian g.fromNormalization`.

Establish `ha : IsProper g.toNormalization`. Establish `: IsProper (g.toNormalization ≫ g.fromNormalization)`. Rewrite using `[g.toNormalization_fromNormalization]`. Conclude with `hg`. Conclude with `IsProper.of_comp _ g.fromNormalization`.

Establish `hbij : ∀ V : g.normalization.Opens, Function.Bijective (g.toNormalization.app V).hom`. Introduce `V`. Use `⟨g.toNormalization.app_injective V, fun t => ?_⟩` and prove the remaining obligations. Take `⟨s, hs⟩` from `GlobalTheory.mem_range_app_of_forall_isAffineOpen g.toNormalization V t fun W hW hWV => by`. Establish `: IsNoetherianRing Γ(g.normalization, W)` using `IsLocallyNoetherian.component_noetherian ⟨W, hW⟩`.

Conclude with `GlobalTheory.mem_range_toNormalization_app g W _ (RingHom.IsIntegral.of_finite (finite_app_of_isProper g.toNormalization hW) _)`. Conclude with `⟨s, hs⟩`. Establish `hs : Surjective g.toNormalization`. Establish `h` using `g.toNormalization.denseRange.closure_range`. Rewrite `h` using `[g.toNormalization.isClosedMap.isClosed_range.closure_eq]`.

Conclude with `⟨Set.range_eq_univ.mp h⟩`. Conclude with `⟨g.normalization, g.toNormalization, g.fromNormalization, g.toNormalization_fromNormalization, hb, ha, hs, hbij, fun y => GlobalTheory.T.zariski_connectedness_isPreconnected_fibre X _ g.toNormalization hY' ha hbij y⟩`.
-/
theorem stein_factorisation : ∀ (X Y : Scheme.{0}) (g : X ⟶ Y), IsLocallyNoetherian Y → IsProper g → ∃ (Y' : Scheme.{0}) (a : X ⟶ Y') (b : Y' ⟶ Y), a ≫ b = g ∧ IsFinite b ∧ IsProper a ∧ Surjective a ∧ (∀ V : Y'.Opens, Function.Bijective (a.app V).hom) ∧ ∀ y : Y', _root_.IsPreconnected {x : X | a x = y} := by
  intro X Y g hY hg
  have hb : IsFinite g.fromNormalization := by
    refine { toIsAffineHom := inferInstance, finite_app := fun U hU => ?_ }
    have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    letI := (g.app U).hom.toAlgebra
    have : Module.Finite Γ(Y, U) Γ(X, g ⁻¹ᵁ U) := finite_app_of_isProper g hU
    have : Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, g ⁻¹ᵁ U)) :=
      Module.IsNoetherian.finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, g ⁻¹ᵁ U)).toSubmodule
    rw [g.fromNormalization_app hU]
    exact (RingHom.finite_respectsIso.cancel_right_isIso _ _).2 (RingHom.finite_algebraMap.2 this)
  have hY' : IsLocallyNoetherian g.normalization := LocallyOfFiniteType.isLocallyNoetherian g.fromNormalization
  have ha : IsProper g.toNormalization := by
    have : IsProper (g.toNormalization ≫ g.fromNormalization) := by
      rw [g.toNormalization_fromNormalization]; exact hg
    exact IsProper.of_comp _ g.fromNormalization
  have hbij : ∀ V : g.normalization.Opens, Function.Bijective (g.toNormalization.app V).hom := by
    intro V
    refine ⟨g.toNormalization.app_injective V, fun t => ?_⟩
    obtain ⟨s, hs⟩ := GlobalTheory.mem_range_app_of_forall_isAffineOpen g.toNormalization V t fun W hW hWV => by
      have : IsNoetherianRing Γ(g.normalization, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
      exact GlobalTheory.mem_range_toNormalization_app g W _
        (RingHom.IsIntegral.of_finite (finite_app_of_isProper g.toNormalization hW) _)
    exact ⟨s, hs⟩
  have hs : Surjective g.toNormalization := by
    have h := g.toNormalization.denseRange.closure_range
    rw [g.toNormalization.isClosedMap.isClosed_range.closure_eq] at h
    exact ⟨Set.range_eq_univ.mp h⟩
  exact ⟨g.normalization, g.toNormalization, g.fromNormalization, g.toNormalization_fromNormalization, hb, ha, hs,
    hbij, fun y => GlobalTheory.T.zariski_connectedness_isPreconnected_fibre X _ g.toNormalization hY' ha hbij y⟩

end GlobalTheory.SteinFact

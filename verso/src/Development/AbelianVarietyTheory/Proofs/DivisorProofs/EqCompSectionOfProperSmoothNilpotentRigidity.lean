import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.OneTmulNeZeroOfDomain
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsNoetherianModelOfSmooth
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoAppTopOfIsAffine
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.EqCompSectionOfSurjectiveAppTop

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Rigidity

/- English proof (translation)
Establish `h` using `_root_.range_comap_of_surjective R₀ π hs`. Establish `h2 : PrimeSpectrum.zeroLocus (RingHom.ker π : Set R) = Set.univ`. Rewrite using `[PrimeSpectrum.zeroLocus_eq_univ_iff]`. Introduce `x hx`. Take `⟨n, hn⟩` from `hn`.

Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `: x ^ n ∈ RingHom.ker π ^ n` using `Ideal.pow_mem_pow hx n`. Rewrite `this` using `[hn]`. Conclude with `(Submodule.mem_bot R).1 this`. Rewrite `h` using `[h2, Set.range_eq_univ]`.

Conclude with `h`.
-/
theorem spMap_surjective {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hs : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π)) :
    Function.Surjective (spMap π) := by
  have h := _root_.range_comap_of_surjective R₀ π hs
  have h2 : PrimeSpectrum.zeroLocus (RingHom.ker π : Set R) = Set.univ := by
    rw [PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro x hx
    obtain ⟨n, hn⟩ := hn
    refine ⟨n, ?_⟩
    have : x ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at this
    exact (Submodule.mem_bot R).1 this
  rw [h2, Set.range_eq_univ] at h
  exact h

/- English proof (translation)
Introduce `R R₀ _ _ π hs hn P X P₀ l hpb hsm hpr hgc ε hε f s₀ hf`. Use `hsm` as an intermediate fact. Use `hpr` as an intermediate fact. Establish `: GeometricallyIntegral P.hom` using `forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.hom hsm hgc`. Establish `hsurj : ∀ V : (Sp R).Opens, Function.Surjective (P.hom.app V).hom` using `fun V => by`.

Use `GlobalFunctions.isIso_app FlatFibreInjective.injective_baseChange exists_noetherian_model_of_smooth P.hom V` as an intermediate fact. Conclude with `(ConcreteCategory.bijective_of_isIso (P.hom.app V)).2`. Establish `hloc : ∀ t : Sp R, ∃ V : (Sp R).Opens, t ∈ V ∧ (P.hom ⁻¹ᵁ V).ι ≫ f.left = (P.hom ⁻¹ᵁ V).ι ≫ P.hom ≫ ε ≫ f.left`. Introduce `t`. Take `⟨t₀, ht₀⟩` from `spMap_surjective π hs hn t`.

Use `local_rigidity _ _ _ P.hom ε f.left hε inferInstance hsurj t (s₀ t₀) ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨z, hz₁, hz₂⟩` from `Scheme.Pullback.exists_preimage_pullback (f := P.hom) (g := spMap π) x t₀ (hx.trans ht₀.symm)`. Establish `e₁ : l (hpb.isoPullback.inv z) = x`. Rewrite using `[← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz₁]`.

Establish `e₂ : P₀.hom (hpb.isoPullback.inv z) = t₀`. Rewrite using `[← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd, hz₂]`. Rewrite using `[← e₁, ← Scheme.Hom.comp_apply, hf, Scheme.Hom.comp_apply, e₂]`. Use `choose V hV hfg using hloc`. Establish `hc : TopologicalSpace.IsOpenCover (fun t => P.hom ⁻¹ᵁ V t)`.

Rewrite using `[TopologicalSpace.IsOpenCover, eq_top_iff]`. Conclude with `fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨P.hom x, hV (P.hom x)⟩`. Conclude with `(P.left.openCoverOfIsOpenCover _ hc).hom_ext _ _ fun t => hfg t`.
-/
theorem eq_comp_section : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (P X : Over (Sp R)) (P₀ : Over (Sp R₀)) (l : P₀.left ⟶ P.left), IsPullback l P₀.hom P.hom (spMap π) →
    Smooth P.hom → IsProper P.hom → GeometricallyConnected P.hom →
    ∀ (ε : Sp R ⟶ P.left), ε ≫ P.hom = 𝟙 _ → ∀ (f : P ⟶ X) (s₀ : Sp R₀ ⟶ X.left), l ≫ f.left = P₀.hom ≫ s₀ →
    f.left = P.hom ≫ ε ≫ f.left := by
  intro R R₀ _ _ π hs hn P X P₀ l hpb hsm hpr hgc ε hε f s₀ hf
  have := hsm
  have := hpr
  have : GeometricallyIntegral P.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.hom hsm hgc
  have hsurj : ∀ V : (Sp R).Opens, Function.Surjective (P.hom.app V).hom := fun V => by
    have := GlobalFunctions.isIso_app FlatFibreInjective.injective_baseChange
      exists_noetherian_model_of_smooth P.hom V
    exact (ConcreteCategory.bijective_of_isIso (P.hom.app V)).2
  have hloc : ∀ t : Sp R, ∃ V : (Sp R).Opens, t ∈ V ∧
      (P.hom ⁻¹ᵁ V).ι ≫ f.left = (P.hom ⁻¹ᵁ V).ι ≫ P.hom ≫ ε ≫ f.left := by
    intro t
    obtain ⟨t₀, ht₀⟩ := spMap_surjective π hs hn t
    refine local_rigidity _ _ _ P.hom ε f.left hε inferInstance hsurj t (s₀ t₀) ?_
    intro x hx
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := P.hom) (g := spMap π) x t₀
      (hx.trans ht₀.symm)
    have e₁ : l (hpb.isoPullback.inv z) = x := by
      rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz₁]
    have e₂ : P₀.hom (hpb.isoPullback.inv z) = t₀ := by
      rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd, hz₂]
    rw [← e₁, ← Scheme.Hom.comp_apply, hf, Scheme.Hom.comp_apply, e₂]
  choose V hV hfg using hloc
  have hc : TopologicalSpace.IsOpenCover (fun t => P.hom ⁻¹ᵁ V t) := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    exact fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨P.hom x, hV (P.hom x)⟩
  exact (P.left.openCoverOfIsOpenCover _ hc).hom_ext _ _ fun t => hfg t

end GlobalTheory.Rigidity

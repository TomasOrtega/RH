import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelOpenNoetherian

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

/- English proof (translation)
Take `⟨⟨T, kO, yT, hT, hk, he⟩, hr⟩` from `h`. Use `⟨⟨T, kO, yT ≫ U.ι, hT, hk, by rw [← Category.assoc, he]⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨w, rfl⟩`. Use `hr ⟨w, rfl⟩` as an intermediate fact. Simplify `this` using `[Scheme.Hom.comp_apply]`.
-/
theorem isTest_comp_opens_ι {p : ℕ} [Fact p.Prime] {X : Scheme.{0}} (U Xw : X.Opens)
    (yb : Sp 𝓞_ℂ_[p] ⟶ U.toScheme) (h : IsTest p (U.ι ⁻¹ᵁ Xw) yb) : IsTest p Xw (yb ≫ U.ι) := by
  obtain ⟨⟨T, kO, yT, hT, hk, he⟩, hr⟩ := h
  refine ⟨⟨T, kO, yT ≫ U.ι, hT, hk, by rw [← Category.assoc, he]⟩, ?_⟩
  rintro _ ⟨w, rfl⟩
  have := hr ⟨w, rfl⟩
  simpa [Scheme.Hom.comp_apply] using this

/- English proof (translation)
Introduce `p n _ X U Xw K x h`. Take `⟨R, _, ξ, J, _, Q, u, hξ, ⟨z, hz⟩, hT⟩` from `h`. Establish `hxU : U.ι x ∈ (U : Set X)` using `by rw [← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩`. Establish `hzU : z ∈ ((ξ ⁻¹ᵁ U : (Sp R).Opens) : Set (Sp R))` using `by show ξ z ∈ U`. Rewrite using `[hz]`.

Conclude with `hxU`. Take `⟨_, ⟨f, rfl⟩, hzf, hfU⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hzU (ξ ⁻¹ᵁ U).isOpen`. Set `ι'` to `algebraMap R (Localization.Away f)`. Establish `hrange : Set.range (spMap ι') = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))` using `PrimeSpectrum.localization_away_comap_range (Localization.Away f) f`. Establish `hsub : Set.range (spMap ι' ≫ ξ) ⊆ Set.range U.ι`.

Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨y, rfl⟩`. Establish `hy : (spMap ι') y ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))` using `hrange ▸ ⟨y, rfl⟩`. Conclude with `hfU hy`. Take `⟨ξ₁, hfac⟩ : ∃ ξ₁ : Sp (Localization.Away f) ⟶ U.toScheme, ξ₁ ≫ U.ι = spMap ι' ≫ ξ` from `⟨_, IsOpenImmersion.lift_fac _ _ hsub⟩`.

Establish `hξ₁ : IsOpenImmersion ξ₁` using `by haveI : IsOpenImmersion (ξ₁ ≫ U.ι) := by rw [hfac]; infer_instance`. Conclude with `IsOpenImmersion.of_comp ξ₁ U.ι`. Set `Q' : J → Localization.Away f` to `fun j => ι' (Q j)`. Establish `hunit : ∀ j, IsUnit (((algebraMap (Localization.Away f) (Localization.Away ((p : Localization.Away f) * Q' j))).comp ι') ((p : R) * Q j))`. Introduce `j`.

Rewrite using `[RingHom.comp_apply, map_mul, map_natCast]`. Conclude with `IsLocalization.Away.algebraMap_isUnit _`. Take `⟨g, hg⟩ : ∃ g : ∀ j, Localization.Away ((p : R) * Q j) →+* Localization.Away ((p : Localization.Away f) * Q' j), ∀ j, (g j).comp (algebraMap R _) = (algebraMap (Localization.Away f) _).comp ι'` from `⟨fun j => IsLocalization.Away.lift ((p : R) * Q j) (hunit j), fun j => IsLocalization.Away.lift_comp _ (hunit j)⟩`. Use `⟨Localization.Away f, inferInstance, ξ₁, J, inferInstance, Q', fun j => Units.map (g j : _ →* _) (u j), hξ₁, ?_, ?_⟩` and prove the remaining obligations. Establish `hz' : z ∈ Set.range (spMap ι')` using `hrange ▸ hzf`.

Take `⟨z', rfl⟩` from `hz'`. Use `⟨z', (Scheme.Hom.isOpenEmbedding U.ι).injective ?_⟩` and prove the remaining obligations. Rewrite using `[← hz, ← Scheme.Hom.comp_apply, hfac, Scheme.Hom.comp_apply]`. Introduce `φ' hφ'`. Establish `heq : spMap (φ'.comp ι') ≫ ξ = (spMap φ' ≫ ξ₁) ≫ U.ι`.

Rewrite using `[Category.assoc, hfac, sp_sp]`. Take `⟨⟨j0, hj0⟩, hall⟩` from `hT (φ'.comp ι') (by rw [heq]; exact isTest_comp_opens_ι U Xw _ hφ')`. Use `⟨⟨j0, hj0⟩, fun j hj ψ' hψ' κ hκ => ?_⟩` and prove the remaining obligations. Use `hall j hj (ψ'.comp (g j)) (by rw [RingHom.comp_assoc, hg j, ← RingHom.comp_assoc, hψ', RingHom.comp_assoc]) κ (by rw [heq]; exact hκ)` as an intermediate fact. Conclude with `this`.
-/
theorem chartAt_opens_restrict : ∀ (p n : ℕ) [Fact p.Prime] (X : Scheme.{0}) (U Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p])
    (x : U.toScheme), ChartAt p n Xw K (U.ι x) → ChartAt p n (U.ι ⁻¹ᵁ Xw) (fun yb => K (yb ≫ U.ι)) x := by
  intro p n _ X U Xw K x h
  obtain ⟨R, _, ξ, J, _, Q, u, hξ, ⟨z, hz⟩, hT⟩ := h
  have hxU : U.ι x ∈ (U : Set X) := by rw [← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩
  have hzU : z ∈ ((ξ ⁻¹ᵁ U : (Sp R).Opens) : Set (Sp R)) := by
    show ξ z ∈ U
    rw [hz]; exact hxU
  obtain ⟨_, ⟨f, rfl⟩, hzf, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hzU (ξ ⁻¹ᵁ U).isOpen
  let ι' := algebraMap R (Localization.Away f)
  have hrange : Set.range (spMap ι') = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
  have hsub : Set.range (spMap ι' ≫ ξ) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    have hy : (spMap ι') y ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := hrange ▸ ⟨y, rfl⟩
    exact hfU hy
  obtain ⟨ξ₁, hfac⟩ : ∃ ξ₁ : Sp (Localization.Away f) ⟶ U.toScheme, ξ₁ ≫ U.ι = spMap ι' ≫ ξ :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hsub⟩
  have hξ₁ : IsOpenImmersion ξ₁ := by
    haveI : IsOpenImmersion (ξ₁ ≫ U.ι) := by rw [hfac]; infer_instance
    exact IsOpenImmersion.of_comp ξ₁ U.ι
  let Q' : J → Localization.Away f := fun j => ι' (Q j)
  have hunit : ∀ j, IsUnit (((algebraMap (Localization.Away f) (Localization.Away ((p : Localization.Away f) * Q' j))).comp ι')
      ((p : R) * Q j)) := by
    intro j
    rw [RingHom.comp_apply, map_mul, map_natCast]
    exact IsLocalization.Away.algebraMap_isUnit _
  obtain ⟨g, hg⟩ : ∃ g : ∀ j, Localization.Away ((p : R) * Q j) →+* Localization.Away ((p : Localization.Away f) * Q' j),
      ∀ j, (g j).comp (algebraMap R _) = (algebraMap (Localization.Away f) _).comp ι' :=
    ⟨fun j => IsLocalization.Away.lift ((p : R) * Q j) (hunit j),
      fun j => IsLocalization.Away.lift_comp _ (hunit j)⟩
  refine ⟨Localization.Away f, inferInstance, ξ₁, J, inferInstance, Q', fun j => Units.map (g j : _ →* _) (u j), hξ₁,
    ?_, ?_⟩
  · have hz' : z ∈ Set.range (spMap ι') := hrange ▸ hzf
    obtain ⟨z', rfl⟩ := hz'
    refine ⟨z', (Scheme.Hom.isOpenEmbedding U.ι).injective ?_⟩
    rw [← hz, ← Scheme.Hom.comp_apply, hfac, Scheme.Hom.comp_apply]
  · intro φ' hφ'
    have heq : spMap (φ'.comp ι') ≫ ξ = (spMap φ' ≫ ξ₁) ≫ U.ι := by
      rw [Category.assoc, hfac, sp_sp]
    obtain ⟨⟨j0, hj0⟩, hall⟩ := hT (φ'.comp ι') (by rw [heq]; exact isTest_comp_opens_ι U Xw _ hφ')
    refine ⟨⟨j0, hj0⟩, fun j hj ψ' hψ' κ hκ => ?_⟩
    have := hall j hj (ψ'.comp (g j))
      (by rw [RingHom.comp_assoc, hg j, ← RingHom.comp_assoc, hψ', RingHom.comp_assoc]) κ (by rw [heq]; exact hκ)
    exact this

end GlobalTheory.FlatModel

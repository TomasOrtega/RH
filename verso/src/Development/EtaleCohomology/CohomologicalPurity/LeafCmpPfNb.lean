import Development.EtaleCohomology.CohomologicalPurity.LeafCmpPf

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.CohomologicalPurity.Cl

/- English proof (translation)
Introduce `X B B₀ _ _ w w₀ h₀ y hy`. Set `W : (Spec (CommRingCat.of B)).Opens` to `w ⁻¹ᵁ w₀.opensRange`. Establish `hs : IsOpen (X` using `PrimeSpectrum B) (W : Set (Spec (CommRingCat.of B))) := W.2`. Establish `hyW : (y : PrimeSpectrum B) ∈ (W : Set (Spec (CommRingCat.of B)))` using `hy`. Take `⟨_, ⟨g, rfl⟩, hyg, hsub⟩` from `(PrimeSpectrum.isTopologicalBasis_basic_opens (R := B)).exists_subset_of_mem_open hyW hs`.

Set `l : B →+* Localization.Away g` to `algebraMap B (Localization.Away g)`. Establish `hr : Set.range (PrimeSpectrum.comap l) = PrimeSpectrum.basicOpen g` using `PrimeSpectrum.localization_away_comap_range (Localization.Away g) g`. Establish `H : Set.range (Spec.map (CommRingCat.ofHom l) ≫ w) ⊆ Set.range w₀`. Introduce and unpack `_ ⟨t, rfl⟩`. Establish `: (Spec.map (CommRingCat.ofHom l)) t ∈ W` using `hsub (by`.

Establish `h1 : PrimeSpectrum.comap l t ∈ Set.range (PrimeSpectrum.comap l)` using `⟨t, rfl⟩`. Rewrite `h1` using `[hr]`. Conclude with `h1)`. Conclude with `this`. Set `u` to `IsOpenImmersion.lift w₀ _ H`.

Use `⟨Localization.Away g, inferInstance, l, (Spec.preimage u).hom, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Scheme.isOpenImmersion_SpecMap_localizationAway (R := CommRingCat.of B) g`. Establish `h2 : (y : PrimeSpectrum B) ∈ Set.range (PrimeSpectrum.comap l)` using `by rw [hr]; exact hyg`. Take `⟨t, ht⟩` from `h2`. Conclude with `⟨show Spec (CommRingCat.of (Localization.Away g)) from t, ht⟩`.

Rewrite using `[CommRingCat.ofHom_hom, Spec.map_preimage]`. Conclude with `(IsOpenImmersion.lift_fac w₀ _ H).symm`.
-/
theorem LeafCmpNb_pf : LeafCmpNb := by
  intro X B B₀ _ _ w w₀ h₀ y hy
  let W : (Spec (CommRingCat.of B)).Opens := w ⁻¹ᵁ w₀.opensRange
  have hs : IsOpen (X := PrimeSpectrum B) (W : Set (Spec (CommRingCat.of B))) := W.2
  have hyW : (y : PrimeSpectrum B) ∈ (W : Set (Spec (CommRingCat.of B))) := hy
  obtain ⟨_, ⟨g, rfl⟩, hyg, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := B)).exists_subset_of_mem_open hyW hs
  let l : B →+* Localization.Away g := algebraMap B (Localization.Away g)
  have hr : Set.range (PrimeSpectrum.comap l) = PrimeSpectrum.basicOpen g :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away g) g
  have H : Set.range (Spec.map (CommRingCat.ofHom l) ≫ w) ⊆ Set.range w₀ := by
    rintro _ ⟨t, rfl⟩
    have : (Spec.map (CommRingCat.ofHom l)) t ∈ W :=
      hsub (by
        have h1 : PrimeSpectrum.comap l t ∈ Set.range (PrimeSpectrum.comap l) := ⟨t, rfl⟩
        rw [hr] at h1; exact h1)
    exact this
  let u := IsOpenImmersion.lift w₀ _ H
  refine ⟨Localization.Away g, inferInstance, l, (Spec.preimage u).hom, ?_, ?_, ?_⟩
  · exact Scheme.isOpenImmersion_SpecMap_localizationAway (R := CommRingCat.of B) g
  · have h2 : (y : PrimeSpectrum B) ∈ Set.range (PrimeSpectrum.comap l) := by rw [hr]; exact hyg
    obtain ⟨t, ht⟩ := h2
    exact ⟨show Spec (CommRingCat.of (Localization.Away g)) from t, ht⟩
  · rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    exact (IsOpenImmersion.lift_fac w₀ _ H).symm

/- English proof (translation)
The claim follows from `LeafCmp_of hMat LeafCmpNb_pf hId`.
-/
theorem LeafCmp_of' (hMat : LeafMat) (hId : LeafCmpId) : LeafCmp := LeafCmp_of hMat LeafCmpNb_pf hId

end LateralTheory.CohomologicalPurity.Cl

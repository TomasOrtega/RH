import Development.EtaleCohomology.EtaleSheaves.FinEtSectionPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.FinOpenPf

/- English proof (translation)
Rewrite using `[PrimeSpectrum.comap_comp, Set.range_comp, PrimeSpectrum.localization_away_comap_range (Localization.Away e) e, PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem e he]`. Conclude with `PrimeSpectrum.isClosedMap_comap_of_isIntegral _ (fun x => Algebra.IsIntegral.isIntegral (R := S) x) _ (PrimeSpectrum.isClosed_zeroLocus _)`.
-/
theorem range_closed (S C : Type) [CommRing S] [CommRing C] [Algebra S C] [Module.Finite S C] (e : C)
    (he : IsIdempotentElem e) :
    IsClosed (Set.range (PrimeSpectrum.comap ((algebraMap C (Localization.Away e)).comp (algebraMap S C)))) := by
  rw [PrimeSpectrum.comap_comp, Set.range_comp,
    PrimeSpectrum.localization_away_comap_range (Localization.Away e) e,
    PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem e he]
  exact PrimeSpectrum.isClosedMap_comap_of_isIntegral _ (fun x => Algebra.IsIntegral.isIntegral (R := S) x) _
    (PrimeSpectrum.isClosed_zeroLocus _)

/- English proof (translation)
Introduce `S C _ _ _ _ e he hoi`. Use `set φ := (algebraMap C (Localization.Away e)).comp (algebraMap S C) with hφ`. Establish `hopen : IsOpen (Set.range (PrimeSpectrum.comap φ))` using `hoi.isOpen_range`. Take `⟨ε, hε, hr⟩` from `PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen ⟨range_closed S C e he, hopen⟩`. Use `⟨ε, hε, hr, ?_⟩` and prove the remaining obligations.

Set `f` to `Spec.map (CommRingCat.ofHom φ)`. Set `g` to `Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away ε)))`. Establish `H : Set.range g ⊆ Set.range f`. Express the relevant statement in the definitionally equal form `Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away ε))) ⊆ Set.range (PrimeSpectrum.comap φ)`. Rewrite using `[PrimeSpectrum.localization_away_comap_range (Localization.Away ε) ε, hr]`.

Set `l` to `IsOpenImmersion.lift f g H`. Use `⟨(Spec.preimage l).hom, ?_⟩` and prove the remaining obligations. Establish `key : CommRingCat.ofHom φ ≫ Spec.preimage l = CommRingCat.ofHom (algebraMap S (Localization.Away ε))`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, Spec.map_preimage]`.

Conclude with `IsOpenImmersion.lift_fac f g H`. Conclude with `congrArg CommRingCat.Hom.hom key`.
-/
theorem FinOpen_of : LateralTheory.E.FinEtSectionPf.FinOpen := by
  intro S C _ _ _ _ e he hoi
  set φ := (algebraMap C (Localization.Away e)).comp (algebraMap S C) with hφ
  have hopen : IsOpen (Set.range (PrimeSpectrum.comap φ)) := hoi.isOpen_range
  obtain ⟨ε, hε, hr⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
    ⟨range_closed S C e he, hopen⟩
  refine ⟨ε, hε, hr, ?_⟩
  let f := Spec.map (CommRingCat.ofHom φ)
  let g := Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away ε)))
  have H : Set.range g ⊆ Set.range f := by
    change Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away ε))) ⊆
      Set.range (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away ε) ε, hr]
  let l := IsOpenImmersion.lift f g H
  refine ⟨(Spec.preimage l).hom, ?_⟩
  have key : CommRingCat.ofHom φ ≫ Spec.preimage l =
      CommRingCat.ofHom (algebraMap S (Localization.Away ε)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact IsOpenImmersion.lift_fac f g H
  exact congrArg CommRingCat.Hom.hom key

end LateralTheory.E.FinOpenPf

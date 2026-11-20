import Development.EtaleCohomology.EtaleSheaves.FinEtSectionPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.PiecesPf

/- English proof (translation)
Establish `w : CommRingCat.ofHom a ≫ CommRingCat.ofHom ρ = CommRingCat.ofHom π ≫ CommRingCat.ofHom b`. Use extensionality with `x`. Conclude with `congrArg (fun f : T →+* C => f x) hcomm`. Use `IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w ?_ ?_ ?_ ?_)` and prove the remaining obligations. Introduce `s`.

Use `CommRingCat.ofHom (ρ.liftOfSurjective hρ ⟨s.inl.hom, ?_⟩)` and prove the remaining obligations. Rewrite using `[hker, Ideal.map_le_iff_le_comap]`. Introduce `t ht`. Establish `h1` using `congrArg (fun f => f.hom t) s.condition`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1`.

Simplify using `only [Ideal.mem_comap, RingHom.mem_ker] at ht ⊢`. Rewrite using `[h1, ht, map_zero]`. Introduce `s`. Use extensionality with `x`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]`.

Conclude with `RingHom.liftOfSurjective_comp_apply ρ hρ _ x`. Introduce `s`. Use extensionality with `x`. Take `⟨t, rfl⟩` from `hπ x`. Establish `h1` using `congrArg (fun f => f.hom t) s.condition`.

Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1 ⊢`. Rewrite using `[← RingHom.comp_apply b π, ← hcomm, RingHom.comp_apply, RingHom.liftOfSurjective_comp_apply]`. Conclude with `h1`. Introduce `s m hm _`. Use extensionality with `x`.

Take `⟨y, rfl⟩` from `hρ x`. Simplify using `only [CommRingCat.hom_ofHom]`. Rewrite using `[RingHom.liftOfSurjective_comp_apply]`. Use `congrArg (fun f => f.hom y) hm` as an intermediate fact. Simplify using `using this`.
-/
lemma sq1 {T S C' C : Type} [CommRing T] [CommRing S] [CommRing C'] [CommRing C]
    (a : T →+* C') (π : T →+* S) (ρ : C' →+* C) (b : S →+* C) (hρ : Function.Surjective ρ) (hπ : Function.Surjective π)
    (hcomm : ρ.comp a = b.comp π) (hker : RingHom.ker ρ = (RingHom.ker π).map a) :
    IsPushout (CommRingCat.ofHom a) (CommRingCat.ofHom π) (CommRingCat.ofHom ρ) (CommRingCat.ofHom b) := by
  have w : CommRingCat.ofHom a ≫ CommRingCat.ofHom ρ = CommRingCat.ofHom π ≫ CommRingCat.ofHom b := by
    ext x; exact congrArg (fun f : T →+* C => f x) hcomm
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w ?_ ?_ ?_ ?_)
  · intro s
    refine CommRingCat.ofHom (ρ.liftOfSurjective hρ ⟨s.inl.hom, ?_⟩)
    rw [hker, Ideal.map_le_iff_le_comap]
    intro t ht
    have h1 := congrArg (fun f => f.hom t) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
    simp only [Ideal.mem_comap, RingHom.mem_ker] at ht ⊢
    rw [h1, ht, map_zero]
  · intro s
    ext x
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    exact RingHom.liftOfSurjective_comp_apply ρ hρ _ x
  · intro s
    ext x
    obtain ⟨t, rfl⟩ := hπ x
    have h1 := congrArg (fun f => f.hom t) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1 ⊢
    rw [← RingHom.comp_apply b π, ← hcomm, RingHom.comp_apply, RingHom.liftOfSurjective_comp_apply]
    exact h1
  · intro s m hm _
    ext x
    obtain ⟨y, rfl⟩ := hρ x
    simp only [CommRingCat.hom_ofHom]
    rw [RingHom.liftOfSurjective_comp_apply]
    have := congrArg (fun f => f.hom y) hm
    simpa using this

/- English proof (translation)
Introduce `_ _ S C _ _ _ _ hQA`. Take `⟨T, _, _, π, hAIC, hπ⟩` from `hQA`. Take `⟨C', _, _, ρ, hEt, hρ, hcomm, hker⟩` from `hL T S C π hπ`. Use `hEt` as an intermediate fact. Take `⟨n, e', he', hoi⟩` from `hA T C' hAIC`.

Use `⟨n, ρ ∘ e', he'.map ρ, fun j => ?_⟩` and prove the remaining obligations. Set `fₘ : Localization.Away (e' j) →+* Localization.Away (ρ (e' j))` to `IsLocalization.Away.map _ _ ρ (e' j)`. Establish `: IsLocalization ((Submonoid.powers (e' j)).map ρ) (Localization.Away (ρ (e' j)))`. Rewrite using `[Submonoid.map_powers]`. Use `infer_instance`.

Establish `H : fₘ.comp (algebraMap C' _) = (algebraMap C _).comp ρ` using `IsLocalization.map_comp _`. Establish `sq2` using `CommRingCat.isPushout_of_isLocalization ρ fₘ H (Submonoid.powers (e' j))`. Establish `sq` using `(sq1 (algebraMap T C') π ρ (algebraMap S C) hρ hπ hcomm hker).paste_horiz sq2.flip`. Establish `pb` using `isPullback_SpecMap_of_isPushout _ _ _ _ sq`. Establish `hj` using `hoi j`.

Rewrite `hj` using `[CommRingCat.ofHom_comp]`. Use `MorphismProperty.of_isPullback (P := @IsOpenImmersion) pb hj` as an intermediate fact. Rewrite using `[CommRingCat.ofHom_comp]`. Conclude with `this`.
-/
theorem Pieces_of (hL : LateralTheory.E.t_E1Cut.EtLift) (hA : LateralTheory.E.t_E1Cut.EtAIC) :
    LateralTheory.E.FinEtSectionPf.Pieces := by
  intro _ _ S C _ _ _ _ hQA
  obtain ⟨T, _, _, π, hAIC, hπ⟩ := hQA
  obtain ⟨C', _, _, ρ, hEt, hρ, hcomm, hker⟩ := hL T S C π hπ
  have := hEt
  obtain ⟨n, e', he', hoi⟩ := hA T C' hAIC
  refine ⟨n, ρ ∘ e', he'.map ρ, fun j => ?_⟩
  let fₘ : Localization.Away (e' j) →+* Localization.Away (ρ (e' j)) :=
    IsLocalization.Away.map _ _ ρ (e' j)
  have : IsLocalization ((Submonoid.powers (e' j)).map ρ) (Localization.Away (ρ (e' j))) := by
    rw [Submonoid.map_powers]; infer_instance
  have H : fₘ.comp (algebraMap C' _) = (algebraMap C _).comp ρ := IsLocalization.map_comp _
  have sq2 := CommRingCat.isPushout_of_isLocalization ρ fₘ H (Submonoid.powers (e' j))
  have sq := (sq1 (algebraMap T C') π ρ (algebraMap S C) hρ hπ hcomm hker).paste_horiz sq2.flip
  have pb := isPullback_SpecMap_of_isPushout _ _ _ _ sq
  have hj := hoi j
  rw [CommRingCat.ofHom_comp] at hj
  have := MorphismProperty.of_isPullback (P := @IsOpenImmersion) pb hj
  rw [CommRingCat.ofHom_comp]
  exact this

end LateralTheory.E.PiecesPf

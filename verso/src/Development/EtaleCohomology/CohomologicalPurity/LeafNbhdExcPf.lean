import Development.EtaleCohomology.CohomologicalPurity.LeafIndExcPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

def nbhdRet {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (hb : Function.Bijective
    (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) : B →+* A ⧸ I :=
  ((RingEquiv.ofBijective _ hb).symm : (B ⧸ I.map φ) →+* A ⧸ I).comp (Ideal.Quotient.mk (I.map φ))

/- English proof (translation)
Unfold `nbhdRet`. Simplify using `only [RingHom.coe_comp, Function.comp_apply]`. Rewrite using `[RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq]`. Simplify using `[Ideal.quotientMap_mk]`.
-/
theorem nbhdRet_comp {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (hb : Function.Bijective
    (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) (a : A) :
    nbhdRet φ I hb (φ a) = Ideal.Quotient.mk I a := by
  unfold nbhdRet
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq]
  simp [Ideal.quotientMap_mk]

/- English proof (translation)
Establish `w : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (nbhdRet φ I hb) = CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ 𝟙 (CommRingCat.of (A ⧸ I))`. Use extensionality with `a`. Simplify using `[nbhdRet_comp]`. Use `IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk _ (fun s => s.inr) ?_ ?_ ?_)` and prove the remaining obligations. Introduce `s`.

Use extensionality with `b`. Take `⟨x, hx⟩` from `hb.2 (Ideal.Quotient.mk (I.map φ) b)`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite `hx` using `[Ideal.quotientMap_mk, Ideal.Quotient.eq]`. Establish `hker : ∀ y ∈ I.map φ, s.inl y = 0`.

Introduce `y hy`. Establish `hle : I.map φ ≤ RingHom.ker s.inl.hom`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `i hi`. Use `congrArg (fun g => g.hom i) s.condition` as an intermediate fact.

Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this`. Simplify using `only [Ideal.mem_comap, RingHom.mem_ker, this, Ideal.Quotient.eq_zero_iff_mem.2 hi, map_zero]`. Conclude with `hle hy`. Establish `h1 : s.inl b = s.inl (φ a)`. Use `hker _ hx` as an intermediate fact.

Rewrite `this` using `[map_sub, sub_eq_zero]`. Conclude with `this.symm`. Establish `h2` using `congrArg (fun g => g.hom a) s.condition`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2`. Establish `h3 : nbhdRet φ I hb b = Ideal.Quotient.mk I a`.

Unfold `nbhdRet`. Simplify using `only [RingHom.coe_comp, Function.comp_apply]`. Rewrite using `[RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq, RingEquiv.ofBijective_apply, Ideal.quotientMap_mk]`. Conclude with `(Ideal.Quotient.eq.2 hx).symm`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]`.

Rewrite using `[h3, h1, h2]`. Introduce `s`. Simplify using the standard rewrite rules. Introduce `s m h1 h2`. Simplify using `using h2`.
-/
theorem nbhd_isPushout {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (hb : Function.Bijective
    (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) :
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (nbhdRet φ I hb)) (𝟙 (CommRingCat.of (A ⧸ I))) := by
  have w : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (nbhdRet φ I hb) =
      CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ 𝟙 (CommRingCat.of (A ⧸ I)) := by
    ext a; simp [nbhdRet_comp]
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk _ (fun s => s.inr) ?_ ?_ ?_)
  · intro s
    ext b
    obtain ⟨x, hx⟩ := hb.2 (Ideal.Quotient.mk (I.map φ) b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hx
    have hker : ∀ y ∈ I.map φ, s.inl y = 0 := by
      intro y hy
      have hle : I.map φ ≤ RingHom.ker s.inl.hom := by
        rw [Ideal.map_le_iff_le_comap]
        intro i hi
        have := congrArg (fun g => g.hom i) s.condition
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
        simp only [Ideal.mem_comap, RingHom.mem_ker, this, Ideal.Quotient.eq_zero_iff_mem.2 hi, map_zero]
      exact hle hy
    have h1 : s.inl b = s.inl (φ a) := by
      have := hker _ hx
      rw [map_sub, sub_eq_zero] at this
      exact this.symm
    have h2 := congrArg (fun g => g.hom a) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
    have h3 : nbhdRet φ I hb b = Ideal.Quotient.mk I a := by
      unfold nbhdRet
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq, RingEquiv.ofBijective_apply, Ideal.quotientMap_mk]
      exact (Ideal.Quotient.eq.2 hx).symm
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    rw [h3, h1, h2]
  · intro s; simp
  · intro s m h1 h2
    simpa using h2

/- English proof (translation)
Use `isPullback_SpecMap_of_isPushout _ _ _ _ (nbhd_isPushout φ I hb)` as an intermediate fact. Simplify using `using this`.
-/
theorem nbhd_isPullback {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (hb : Function.Bijective
    (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) :
    IsPullback (Spec.map (CommRingCat.ofHom (nbhdRet φ I hb))) (𝟙 _) (Spec.map (CommRingCat.ofHom φ))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
  have := isPullback_SpecMap_of_isPushout _ _ _ _ (nbhd_isPushout φ I hb)
  simpa using this

/- English proof (translation)
Use extensionality with `x`. Express the relevant statement in the definitionally equal form `x ∈ (PrimeSpectrum.zeroLocus (I : Set A))ᶜ ↔ x ∈ (Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)))ᶜ`. Rewrite using `[range_comap_of_surjective _ _ (Ideal.Quotient.mk_surjective (I := I)), Ideal.mk_ker]`.
-/
theorem range_spec_quot {A : Type} [CommRing A] (I : Ideal A) :
    (off A I : Set (Spec (CommRingCat.of A))) = (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))ᶜ := by
  ext x
  change x ∈ (PrimeSpectrum.zeroLocus (I : Set A))ᶜ ↔ x ∈ (Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)))ᶜ
  rw [range_comap_of_surjective _ _ (Ideal.Quotient.mk_surjective (I := I)), Ideal.mk_ker]

/- English proof (translation)
Introduce `a1 q A B _ _ φ I hN hq h`. Take `⟨het, hb⟩` from `hN`. Establish `: Etale (Spec.map (CommRingCat.ofHom φ))` using `HasRingHomProperty.Spec_iff.2 het`. Establish `: IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))` using `IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective`. Conclude with `hE a1 q (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom (nbhdRet φ I hb))) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) (nbhd_isPullback φ I hb) _ _ (range_spec_quot I) (off_map φ I)`.
-/
theorem leafNbhdExc_of (hE : LeafExc) : LeafNbhdExc := by
  intro a1 q A B _ _ φ I hN hq h
  obtain ⟨het, hb⟩ := hN
  have : Etale (Spec.map (CommRingCat.ofHom φ)) := HasRingHomProperty.Spec_iff.2 het
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact hE a1 q (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom (nbhdRet φ I hb)))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) (nbhd_isPullback φ I hb) _ _ (range_spec_quot I)
    (off_map φ I)

end LateralTheory.CohomologicalPurity

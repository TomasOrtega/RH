import Development.EtaleCohomology.CohomologicalPurity.LeafClCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.NbPf

variable {A B : Type} [CommRing A] [CommRing B]

def psi (φ : A →+* B) (I : Ideal A) (hb : Function.Bijective (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) :
    B →+* A ⧸ I :=
  (RingEquiv.ofBijective _ hb).symm.toRingHom.comp (Ideal.Quotient.mk (I.map φ))

/- English proof (translation)
Use extensionality with `a`. Simplify using `only [psi, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]`. Rewrite using `[RingEquiv.symm_apply_eq]`. Simplify using `[RingEquiv.ofBijective_apply, Ideal.quotientMap_mk]`.
-/
theorem psi_comp (φ : A →+* B) (I : Ideal A) (hb) : (psi φ I hb).comp φ = Ideal.Quotient.mk I := by
  ext a
  simp only [psi, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [RingEquiv.symm_apply_eq]
  simp [RingEquiv.ofBijective_apply, Ideal.quotientMap_mk]

/- English proof (translation)
Use `⟨⟨by ext a; simpa using congrArg (fun f => f a) (psi_comp φ I hb)⟩, ⟨PushoutCocone.IsColimit.mk _ (fun s => s.inr) ?_ ?_ ?_⟩⟩` and prove the remaining obligations. Introduce `s`. Establish `hk : I.map φ ≤ RingHom.ker s.inl.hom`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `i hi`.

Use `congrArg (fun f => f.hom i) s.condition` as an intermediate fact. Simplify using `only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this`. Simplify using `[RingHom.mem_ker, this, Ideal.Quotient.eq_zero_iff_mem.mpr hi]`. Use extensionality with `b`. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (psi φ I hb b)`.

Establish `e1 : Ideal.Quotient.mk (I.map φ) (φ a) = Ideal.Quotient.mk (I.map φ) b`. Establish `: (RingEquiv.ofBijective _ hb) (psi φ I hb b) = Ideal.Quotient.mk (I.map φ) b`. Simplify using `[psi]`. Rewrite using `[← this, ← ha]`. Simplify using `[RingEquiv.ofBijective_apply, Ideal.quotientMap_mk]`.

Rewrite `e1` using `[Ideal.Quotient.eq]`. Establish `e2 : s.inl.hom (φ a) = s.inl.hom b`. Use `hk e1` as an intermediate fact. Rewrite `this` using `[RingHom.mem_ker, map_sub, sub_eq_zero]`. Conclude with `this`.

Establish `e3` using `congrArg (fun f => f.hom a) s.condition`. Simplify using `only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at e3`. Simplify using `only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, ← ha]`. Rewrite using `[← e2, e3]`. Introduce `s`.

Simplify using the standard rewrite rules. Introduce `s m _ h2`. Simplify using `using h2`.
-/
theorem isPushout_psi (φ : A →+* B) (I : Ideal A) (hb) :
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (psi φ I hb)) (𝟙 (CommRingCat.of (A ⧸ I))) := by
  refine ⟨⟨by ext a; simpa using congrArg (fun f => f a) (psi_comp φ I hb)⟩, ⟨PushoutCocone.IsColimit.mk _
    (fun s => s.inr) ?_ ?_ ?_⟩⟩
  · intro s
    have hk : I.map φ ≤ RingHom.ker s.inl.hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro i hi
      have := congrArg (fun f => f.hom i) s.condition
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
      simp [RingHom.mem_ker, this, Ideal.Quotient.eq_zero_iff_mem.mpr hi]
    ext b
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (psi φ I hb b)
    have e1 : Ideal.Quotient.mk (I.map φ) (φ a) = Ideal.Quotient.mk (I.map φ) b := by
      have : (RingEquiv.ofBijective _ hb) (psi φ I hb b) = Ideal.Quotient.mk (I.map φ) b := by
        simp [psi]
      rw [← this, ← ha]; simp [RingEquiv.ofBijective_apply, Ideal.quotientMap_mk]
    rw [Ideal.Quotient.eq] at e1
    have e2 : s.inl.hom (φ a) = s.inl.hom b := by
      have := hk e1; rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this; exact this
    have e3 := congrArg (fun f => f.hom a) s.condition
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at e3
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, ← ha]
    rw [← e2, e3]
  · intro s; simp
  · intro s m _ h2; simpa using h2

/- English proof (translation)
Introduce `hA1 q A B _ _ φ I J hN hJ h`. Substitute `hJ` using the available equality. Take `⟨he, hb⟩` from `hN`. Establish `: Etale (Spec.map (CommRingCat.ofHom φ))` using `HasRingHomProperty.Spec_iff.mpr he`. Establish `: IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))` using `IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective`.

Establish `hP` using `isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_psi φ I hb)`. Rewrite `hP` using `[Spec.map_id]`. Use `hE hA1 q (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom (psi φ I hb))) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) hP (off B (I.map φ)) (off A I) ?_ (Cl.off_map φ I)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(PrimeSpectrum.zeroLocus (I : Set A))ᶜ = _`. Use `congr 1`.

Establish `hr` using `range_comap_of_surjective _ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective`. Rewrite `hr` using `[Ideal.mk_ker]`. Rewrite using `[← hr]`. Both sides reduce to the same expression.
-/
theorem nb (hE : LeafExc) : Cl.LeafNb := by
  intro hA1 q A B _ _ φ I J hN hJ h
  subst hJ
  obtain ⟨he, hb⟩ := hN
  have : Etale (Spec.map (CommRingCat.ofHom φ)) := HasRingHomProperty.Spec_iff.mpr he
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hP := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_psi φ I hb)
  rw [Spec.map_id] at hP
  refine hE hA1 q (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom (psi φ I hb)))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) hP (off B (I.map φ)) (off A I) ?_ (Cl.off_map φ I)
  change (PrimeSpectrum.zeroLocus (I : Set A))ᶜ = _
  congr 1
  have hr := range_comap_of_surjective _ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker] at hr
  rw [← hr]; rfl

end LateralTheory.CohomologicalPurity.NbPf

/- English proof (translation)
The claim follows from `LateralTheory.CohomologicalPurity.NbPf.nb hE`.
-/
theorem LateralTheory.CohomologicalPurity.Cl.LeafNb_of (hE : LateralTheory.CohomologicalPurity.LeafExc) : LateralTheory.CohomologicalPurity.Cl.LeafNb := LateralTheory.CohomologicalPurity.NbPf.nb hE

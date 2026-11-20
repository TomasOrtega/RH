import Development.EtaleCohomology.EtaleSheaves.IntPBPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.IntFibPf

/- English proof (translation)
Introduce `n`. Establish `: (pull R (f ≫ g) F n : H R E'' F n → H R E F n) = pull R f F n ∘ pull R g F n`. Use function extensionality and compare the values at `x`. Conclude with `pull_comp R f g F n x`. Rewrite using `[this]`.

Conclude with `(hf n).comp (hg n)`.
-/
lemma eqv_comp {R : Type} [CommRing R] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (F : Shv R)
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have : (pull R (f ≫ g) F n : H R E'' F n → H R E F n) = pull R f F n ∘ pull R g F n := by
    funext x; exact pull_comp R f g F n x
  rw [this]; exact (hf n).comp (hg n)

/- English proof (translation)
Introduce `n`. Use `Function.bijective_iff_has_inverse.mpr ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← pull_comp, e.inv_hom_id, pull_id]`. Rewrite using `[← pull_comp, e.hom_inv_id, pull_id]`.
-/
lemma eqv_iso {R : Type} [CommRing R] {E E' : Spc} (e : E ≅ E') (F : Shv R) : Eqv R e.hom F := by
  intro n
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

/- English proof (translation)
Establish `w : CommSq ψ (CommRingCat.ofHom (IsLocalRing.residue A)) (CommRingCat.ofHom (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map ψ.hom))) (CommRingCat.ofHom (Ideal.quotientMap ((IsLocalRing.maximalIdeal A).map ψ.hom) ψ.hom Ideal.le_comap_map : IsLocalRing.ResidueField A →+* _))` using `by constructor; ext a; rfl`. Use `IsPushout.of_isColimit' w (PushoutCocone.IsColimit.mk _ (fun s => CommRingCat.ofHom (Ideal.Quotient.lift ((IsLocalRing.maximalIdeal A).map ψ.hom) s.inl.hom ?_)) ?_ ?_ ?_)` and prove the remaining obligations. Name the introduced variables `s`. Introduce `a ha`. Establish `hle : ((IsLocalRing.maximalIdeal A).map ψ.hom) ≤ RingHom.ker s.inl.hom`.

Use `Ideal.map_le_iff_le_comap.mpr fun x hx => ?_` and prove the remaining obligations. Establish `h1` using `congrArg (fun f => f.hom x) s.condition`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1`. Simplify using `only [Ideal.mem_comap, RingHom.mem_ker, h1, (IsLocalRing.residue_eq_zero_iff x).mpr hx, map_zero]`. Conclude with `hle ha`.

Introduce `s`. Use extensionality with `b`. Both sides reduce to the same expression. Introduce `s`. Use extensionality with `x`.

Take `⟨a, rfl⟩` from `IsLocalRing.residue_surjective x`. Establish `h1` using `congrArg (fun f => f.hom a) s.condition`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1`. Conclude with `h1`. Introduce `s m h1 h2`.

Use extensionality with `b`. Use `congrArg (fun f => f.hom b) h1` as an intermediate fact. Conclude with `this`.
-/
lemma isPushout_quot (A : Type) [CommRing A] [IsLocalRing A] {B : CommRingCat.{0}} (ψ : CommRingCat.of A ⟶ B) :
    IsPushout ψ (CommRingCat.ofHom (IsLocalRing.residue A))
      (CommRingCat.ofHom (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map ψ.hom)))
      (CommRingCat.ofHom (Ideal.quotientMap ((IsLocalRing.maximalIdeal A).map ψ.hom) ψ.hom Ideal.le_comap_map
        : IsLocalRing.ResidueField A →+* _)) := by
  have w : CommSq ψ (CommRingCat.ofHom (IsLocalRing.residue A)) (CommRingCat.ofHom (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map ψ.hom)))
      (CommRingCat.ofHom (Ideal.quotientMap ((IsLocalRing.maximalIdeal A).map ψ.hom) ψ.hom Ideal.le_comap_map : IsLocalRing.ResidueField A →+* _)) := by
    constructor; ext a; rfl
  refine IsPushout.of_isColimit' w (PushoutCocone.IsColimit.mk _ (fun s => CommRingCat.ofHom
      (Ideal.Quotient.lift ((IsLocalRing.maximalIdeal A).map ψ.hom) s.inl.hom ?_)) ?_ ?_ ?_)
  · rename_i s; intro a ha
    have hle : ((IsLocalRing.maximalIdeal A).map ψ.hom) ≤ RingHom.ker s.inl.hom := by
      refine Ideal.map_le_iff_le_comap.mpr fun x hx => ?_
      have h1 := congrArg (fun f => f.hom x) s.condition
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
      simp only [Ideal.mem_comap, RingHom.mem_ker, h1,
        (IsLocalRing.residue_eq_zero_iff x).mpr hx, map_zero]
    exact hle ha
  · intro s; ext b; rfl
  · intro s; ext x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    have h1 := congrArg (fun f => f.hom a) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
    exact h1
  · intro s m h1 h2
    ext b
    have := congrArg (fun f => f.hom b) h1
    exact this

/- English proof (translation)
Introduce `A _ _ X p hp`. Establish `: IsAffine X` using `isAffine_of_isAffineHom p`. Take `⟨ψ, hψ⟩` from `Spec.map_surjective (X.isoSpec.inv ≫ p)`. Use `⟨Γ(X, ⊤), inferInstance, ψ.hom, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← IsIntegralHom.SpecMap_iff, hψ]`.

Use `infer_instance`. Introduce `q i h`. Establish `hP` using `isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quot A ψ)`. Establish `hP' : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map ψ.hom))) ≫ X.isoSpec.inv) _ p (LateralTheory.E.t_E2Cut.cpt A)` using `hP.of_iso (Iso.refl _) X.isoSpec.symm (Iso.refl _) (Iso.refl _) (by simp) ((Category.comp_id _).trans (Category.id_comp _).symm) (by simp [hψ]) (by simp)`. Rewrite using `[← hP'.isoPullback_inv_fst, Functor.map_comp, Functor.map_comp]`.

Conclude with `eqv_comp _ _ _ (eqv_iso (sch.mapIso hP'.isoPullback.symm) _) (eqv_comp _ _ _ h (eqv_iso (sch.mapIso X.isoSpec.symm) _))`.
-/
theorem IntFib_of : LateralTheory.E.IntPBPf.IntFib := by
  intro A _ _ X p hp
  have : IsAffine X := isAffine_of_isAffineHom p
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ p)
  refine ⟨Γ(X, ⊤), inferInstance, ψ.hom, ?_, ?_⟩
  · rw [← IsIntegralHom.SpecMap_iff, hψ]; infer_instance
  · intro q i h
    have hP := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quot A ψ)
    have hP' : IsPullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map ψ.hom))) ≫ X.isoSpec.inv) _ p
        (LateralTheory.E.t_E2Cut.cpt A) :=
      hP.of_iso (Iso.refl _) X.isoSpec.symm (Iso.refl _) (Iso.refl _) (by simp)
        ((Category.comp_id _).trans (Category.id_comp _).symm)
        (by simp [hψ]) (by simp)
    rw [← hP'.isoPullback_inv_fst, Functor.map_comp, Functor.map_comp]
    exact eqv_comp _ _ _ (eqv_iso (sch.mapIso hP'.isoPullback.symm) _)
      (eqv_comp _ _ _ h (eqv_iso (sch.mapIso X.isoSpec.symm) _))

end LateralTheory.E.IntFibPf

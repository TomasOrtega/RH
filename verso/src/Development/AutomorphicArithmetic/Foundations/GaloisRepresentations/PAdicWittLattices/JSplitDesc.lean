import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitDesc

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3 MorphismProperty
universe u v

set_option backward.isDefEq.respectTransparency.types false in
/- English proof (translation)
Establish `hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) j` using `⟨⟨inferInstance, inferInstance⟩, inferInstance⟩`. Establish `hUC : UniversallyClosed g` using `of_isPullback_of_descendsAlong h.flip hQ (inferInstanceAs (UniversallyClosed f))`. Establish `hLFT : LocallyOfFiniteType g` using `of_isPullback_of_descendsAlong h.flip hQ (inferInstanceAs (LocallyOfFiniteType f))`. Establish `hD : MorphismProperty.diagonal @UniversallyClosed g`. Use `of_isPullback_of_descendsAlong (P := MorphismProperty.diagonal @UniversallyClosed) h.flip hQ ?_` and prove the remaining obligations.

Rewrite using `[MorphismProperty.diagonal_iff]`. Use `infer_instance`. Rewrite `hD` using `[MorphismProperty.diagonal_iff]`. Establish `hP : IsProper (pullback.diagonal g)` using `IsProper.mk`. Establish `hC : IsClosedImmersion (pullback.diagonal g)` using `(IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨hP, inferInstance⟩`.

Use `haveI : IsSeparated g := ⟨hC⟩`. Conclude with `IsProper.mk`.
-/
private theorem isProper_desc {A G U Z : Scheme.{0}} {φ : A ⟶ G} {f : A ⟶ U} {g : G ⟶ Z} {j : U ⟶ Z}
    [Flat j] [Surjective j] [QuasiCompact j] (h : IsPullback φ f g j) [IsProper f] : IsProper g := by
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) j :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hUC : UniversallyClosed g :=
    of_isPullback_of_descendsAlong h.flip hQ (inferInstanceAs (UniversallyClosed f))
  have hLFT : LocallyOfFiniteType g :=
    of_isPullback_of_descendsAlong h.flip hQ (inferInstanceAs (LocallyOfFiniteType f))
  have hD : MorphismProperty.diagonal @UniversallyClosed g := by
    refine of_isPullback_of_descendsAlong (P := MorphismProperty.diagonal @UniversallyClosed) h.flip hQ ?_
    rw [MorphismProperty.diagonal_iff]
    infer_instance
  rw [MorphismProperty.diagonal_iff] at hD
  have hP : IsProper (pullback.diagonal g) := IsProper.mk
  have hC : IsClosedImmersion (pullback.diagonal g) :=
    (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨hP, inferInstance⟩
  haveI : IsSeparated g := ⟨hC⟩
  exact IsProper.mk

set_option backward.isDefEq.respectTransparency.types false in
/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => haveI := Function.isEmpty (sigmaMk (fun _ : Fin 0 => W)).symm infer_instance`. Consider the case `succ n ih`. Set `t` to `extendCofanIsColimit (fun _ : Fin (n + 1) => W) (coproductIsCoproduct fun _ : Fin n => W) (coprodIsCoprod W (∐ fun _ : Fin n => W))`. Set `e : (∐ fun _ : Fin (n + 1) => W) ≅ W ⨿ (∐ fun _ : Fin n => W)` to `(coproductIsCoproduct fun _ : Fin (n + 1) => W).coconePointUniqueUpToIso t`.

Establish `key : (Sigma.desc (f` using `fun _ : Fin (n + 1) => W) fun _ => 𝟙 W) = e.hom ≫ coprod.desc (𝟙 W) (Sigma.desc (f := fun _ : Fin n => W) fun _ => 𝟙 W) := by`. Use `Sigma.hom_ext _ _ fun j => ?_` and prove the remaining obligations. Establish `hj` using `IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct (fun _ : Fin (n + 1) => W)) t ⟨j⟩`. Rewrite using `[Sigma.ι_desc, ← Category.assoc]`. Use `erw [hj]`.

Use `Fin.cases ?_ (fun i => ?_) j` and prove the remaining obligations. Simplify using `only [extendCofan, Cofan.mk_ι_app, Fin.cases_zero]`. Conclude with `(coprod.inl_desc _ _).symm`. Simplify using `only [extendCofan, Cofan.mk_ι_app, Fin.cases_succ] show 𝟙 W = (Sigma.ι (fun _ : Fin n => W) i ≫ coprod.inr) ≫ coprod.desc (𝟙 W) (Sigma.desc (f := fun _ : Fin n => W) fun _ => 𝟙 W)`. Rewrite using `[Category.assoc, coprod.inr_desc, Sigma.ι_desc]`.

Rewrite using `[key]`. Use `infer_instance`.
-/
private theorem isFinite_desc_fin (W : Scheme.{0}) (n : ℕ) :
    IsFinite (Sigma.desc (f := fun _ : Fin n => W) fun _ => 𝟙 W) := by
  induction n with
  | zero =>
    haveI := Function.isEmpty (sigmaMk (fun _ : Fin 0 => W)).symm
    infer_instance
  | succ n ih =>
    let t := extendCofanIsColimit (fun _ : Fin (n + 1) => W) (coproductIsCoproduct fun _ : Fin n => W)
      (coprodIsCoprod W (∐ fun _ : Fin n => W))
    let e : (∐ fun _ : Fin (n + 1) => W) ≅ W ⨿ (∐ fun _ : Fin n => W) :=
      (coproductIsCoproduct fun _ : Fin (n + 1) => W).coconePointUniqueUpToIso t
    have key : (Sigma.desc (f := fun _ : Fin (n + 1) => W) fun _ => 𝟙 W) =
        e.hom ≫ coprod.desc (𝟙 W) (Sigma.desc (f := fun _ : Fin n => W) fun _ => 𝟙 W) := by
      refine Sigma.hom_ext _ _ fun j => ?_
      have hj := IsColimit.comp_coconePointUniqueUpToIso_hom
        (coproductIsCoproduct (fun _ : Fin (n + 1) => W)) t ⟨j⟩
      rw [Sigma.ι_desc, ← Category.assoc]
      erw [hj]
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [extendCofan, Cofan.mk_ι_app, Fin.cases_zero]
        exact (coprod.inl_desc _ _).symm
      · simp only [extendCofan, Cofan.mk_ι_app, Fin.cases_succ]
        show 𝟙 W = (Sigma.ι (fun _ : Fin n => W) i ≫ coprod.inr) ≫
          coprod.desc (𝟙 W) (Sigma.desc (f := fun _ : Fin n => W) fun _ => 𝟙 W)
        rw [Category.assoc, coprod.inr_desc, Sigma.ι_desc]
    rw [key]
    infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/- English proof (translation)
Take `⟨n, ⟨e⟩⟩` from `Finite.exists_equiv_fin J`. Establish `key : (Sigma.desc (f` using `fun _ : J => W) fun _ => 𝟙 W) = (Sigma.reindex e.symm (fun _ : J => W)).inv ≫ (Sigma.desc (f := fun _ : Fin n => W) fun _ => 𝟙 W) := by`. Use `Sigma.hom_ext _ _ fun j => ?_` and prove the remaining obligations. Rewrite using `[Sigma.ι_desc, ← Category.assoc]`. Establish `h` using `Sigma.ι_reindex_inv e.symm (fun _ : J => W) (e j)`.

Simplify using `only [Equiv.symm_apply_apply] at h`. Rewrite using `[h]`. Conclude with `(Sigma.ι_desc (f := fun _ : Fin n => W) (fun _ => 𝟙 W) (e j)).symm`. Rewrite using `[key]`. Use `haveI := isFinite_desc_fin W n`.

Use `infer_instance`.
-/
private theorem isFinite_desc (W : Scheme.{0}) (J : Type) [Finite J] :
    IsFinite (Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have key : (Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W) =
      (Sigma.reindex e.symm (fun _ : J => W)).inv ≫ (Sigma.desc (f := fun _ : Fin n => W) fun _ => 𝟙 W) := by
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [Sigma.ι_desc, ← Category.assoc]
    have h := Sigma.ι_reindex_inv e.symm (fun _ : J => W) (e j)
    simp only [Equiv.symm_apply_apply] at h
    rw [h]
    exact (Sigma.ι_desc (f := fun _ : Fin n => W) (fun _ => 𝟙 W) (e j)).symm
  rw [key]
  haveI := isFinite_desc_fin W n
  infer_instance

/- English proof (translation)
Establish `hf : affineLocally RingHom.Etale f`. Rewrite using `[← HasRingHomProperty.eq_affineLocally @Etale]`. Conclude with `‹Etale f›`. Rewrite using `[HasRingHomProperty.eq_affineLocally @LocallyQuasiFinite]`. Use `affineLocally_le (fun {R S} _ _ {g} hg => ?_) f hf` and prove the remaining obligations.

Use `letI : Algebra R S := RingHom.toAlgebra g`. Establish `: Algebra.Etale R S` using `hg`. Use `show Algebra.QuasiFinite R S`. Use `infer_instance`.
-/
private theorem locallyQuasiFinite_of_etale {X Y : Scheme.{0}} (f : X ⟶ Y) [Etale f] : LocallyQuasiFinite f := by
  have hf : affineLocally RingHom.Etale f := by
    rw [← HasRingHomProperty.eq_affineLocally @Etale]
    exact ‹Etale f›
  rw [HasRingHomProperty.eq_affineLocally @LocallyQuasiFinite]
  refine affineLocally_le (fun {R S} _ _ {g} hg => ?_) f hf
  letI : Algebra R S := RingHom.toAlgebra g
  have : Algebra.Etale R S := hg
  show Algebra.QuasiFinite R S
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/- English proof (translation)
Introduce `Z Y W s c _ _ _ J _ σ hs`. Take `⟨hσ, hiso⟩` from `hs`. Use `haveI : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)`. Establish `key : pullback.snd s c = inv (Sigma.desc fun j => pullback.lift (σ j) (𝟙 W) (by rw [hσ j, Category.id_comp])) ≫ Sigma.desc (f` using `fun _ : J => W) fun _ => 𝟙 W := by`. Rewrite using `[IsIso.eq_inv_comp]`.

Use `Sigma.hom_ext _ _ fun j => ?_` and prove the remaining obligations. Rewrite using `[Sigma.ι_desc_assoc, pullback.lift_snd, Sigma.ι_desc]`. Use `haveI : IsFinite (Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W) := isFinite_desc W J`. Use `haveI : Etale (Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W) := IsZariskiLocalAtSource.sigmaDesc (fun _ => inferInstance)`. Use `haveI : IsFinite (pullback.snd s c) := by rw [key]; infer_instance`.

Use `haveI : Etale (pullback.snd s c) := by rw [key]; infer_instance`. Establish `hpb` using `IsPullback.of_hasPullback s c`. Establish `hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) c` using `⟨⟨inferInstance, inferInstance⟩, inferInstance⟩`. Use `haveI : IsProper s := isProper_desc hpb`. Establish `hE : Etale s` using `of_isPullback_of_descendsAlong hpb.flip hQ (inferInstanceAs (Etale (pullback.snd s c)))`.

Use `haveI := hE`. Use `haveI := locallyQuasiFinite_of_etale s`. Conclude with `⟨(IsFinite.iff_isProper_and_locallyQuasiFinite s).mpr ⟨inferInstance, inferInstance⟩, hE⟩`.
-/
theorem UpperTheory.Gal.G3.jSplitDesc :
    SplitDesc := by
  intro Z Y W s c _ _ _ J _ σ hs
  obtain ⟨hσ, hiso⟩ := hs
  haveI : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  have key : pullback.snd s c =
      inv (Sigma.desc fun j => pullback.lift (σ j) (𝟙 W) (by rw [hσ j, Category.id_comp])) ≫
        Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W := by
    rw [IsIso.eq_inv_comp]
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [Sigma.ι_desc_assoc, pullback.lift_snd, Sigma.ι_desc]
  haveI : IsFinite (Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W) := isFinite_desc W J
  haveI : Etale (Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W) :=
    IsZariskiLocalAtSource.sigmaDesc (fun _ => inferInstance)
  haveI : IsFinite (pullback.snd s c) := by rw [key]; infer_instance
  haveI : Etale (pullback.snd s c) := by rw [key]; infer_instance
  have hpb := IsPullback.of_hasPullback s c
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) c :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  haveI : IsProper s := isProper_desc hpb
  have hE : Etale s := of_isPullback_of_descendsAlong hpb.flip hQ (inferInstanceAs (Etale (pullback.snd s c)))
  haveI := hE
  haveI := locallyQuasiFinite_of_etale s
  exact ⟨(IsFinite.iff_isProper_and_locallyQuasiFinite s).mpr ⟨inferInstance, inferInstance⟩, hE⟩

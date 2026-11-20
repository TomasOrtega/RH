import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

noncomputable section
namespace LateralTheory.CohomologicalPurity.TubeCut

instance sch_preservesPullbacks : PreservesLimitsOfShape WalkingCospan sch :=
  inferInstanceAs (PreservesLimitsOfShape WalkingCospan (yoneda ⋙ SimplicialObject.const PSh))

/- English proof (translation)
Establish `e : h₁.isoPullback.hom ≫ pbRel g a π' π h = k ≫ h₀.isoPullback.hom`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [pbRel, Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc, kf]`. Simplify using `only [pbRel, Category.assoc, pullback.lift_snd, IsPullback.isoPullback_hom_snd, kz, Category.comp_id]`. Establish `e' : pbRel g a π' π h = h₁.isoPullback.inv ≫ k ≫ h₀.isoPullback.hom`.

Rewrite using `[← e, Iso.inv_hom_id_assoc]`. Rewrite using `[e']`. Use `infer_instance`.
-/
theorem pbRel_isIso_of {B G E' E Q₁ Q₀ : Spc} (g : G ⟶ B) (a : E' ⟶ E) (π' : E' ⟶ B) (π : E ⟶ B) (h : a ≫ π = π')
    {f₁ : Q₁ ⟶ E'} {z₁ : Q₁ ⟶ G} {f₀ : Q₀ ⟶ E} {z₀ : Q₀ ⟶ G} (h₁ : IsPullback f₁ z₁ π' g) (h₀ : IsPullback f₀ z₀ π g)
    (k : Q₁ ⟶ Q₀) [IsIso k] (kf : k ≫ f₀ = f₁ ≫ a) (kz : k ≫ z₀ = z₁) : IsIso (pbRel g a π' π h) := by
  have e : h₁.isoPullback.hom ≫ pbRel g a π' π h = k ≫ h₀.isoPullback.hom := by
    apply pullback.hom_ext
    · simp only [pbRel, Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc, kf]
    · simp only [pbRel, Category.assoc, pullback.lift_snd, IsPullback.isoPullback_hom_snd, kz, Category.comp_id]
  have e' : pbRel g a π' π h = h₁.isoPullback.inv ≫ k ≫ h₀.isoPullback.hom := by
    rw [← e, Iso.inv_hom_id_assoc]
  rw [e']; infer_instance

/- English proof (translation)
Establish `: IsIso (CommRingCat.ofHom f)` using `(RingEquiv.ofBijective f hb).toCommRingCatIso.isIso_hom`. Use `infer_instance`.
-/
theorem isIso_specMap_of_bij {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hb : Function.Bijective f) :
    IsIso (Spec.map (CommRingCat.ofHom f)) := by
  have : IsIso (CommRingCat.ofHom f) := (RingEquiv.ofBijective f hb).toCommRingCatIso.isIso_hom
  infer_instance

/- English proof (translation)
Substitute `e` using the available equality. Substitute `hK` using the available equality. Conclude with `hb`.
-/
theorem quot_bij_of_eq {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I J : Ideal A) (e : J = I) (K : Ideal B)
    (hK : K = I.map φ) (h : J ≤ K.comap φ) (hb : Function.Bijective (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) :
    Function.Bijective (Ideal.quotientMap K φ h) := by
  subst e; subst hK; exact hb

/- English proof (translation)
Introduce `H d P V h`. Use `P.cl` as an intermediate fact. Use `set A := Γ(P.X, V.1)`. Use `set I := P.ι.ker.ideal V`. Use `set φ : A →+* H.obj A I := eta H P V`.

Take `⟨⟨z₁, h₁⟩, -⟩` from `hZ P.X P.Z P.ι V (H.obj A I) φ`. Take `⟨⟨z₀, h₀'⟩, -⟩` from `hZ P.X P.Z P.ι V A (RingHom.id A)`. Establish `e₀ : Spec.map (CommRingCat.ofHom (RingHom.id A)) ≫ V.2.fromSpec = V.2.fromSpec` using `by simp`. Rewrite `h₀'` using `[e₀]`. Establish `hle : I.map (RingHom.id A) ≤ (I.map φ).comap φ` using `by rw [Ideal.map_id]; exact Ideal.le_comap_map`.

Use `set qm := Ideal.quotientMap (I.map φ) φ hle`. Establish `hb : Function.Bijective qm` using `quot_bij_of_eq φ I _ (Ideal.map_id I) _ rfl hle (hQ A (H.obj A I) φ I (H.ind A I))`. Establish `hcomp : qm.comp (Ideal.Quotient.mk (I.map (RingHom.id A))) = (Ideal.Quotient.mk (I.map φ)).comp φ` using `Ideal.quotientMap_comp_mk hle`. Establish `kf : Spec.map (CommRingCat.ofHom qm) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (RingHom.id A)))) = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ))) ≫ Spec.map (CommRingCat.ofHom φ)`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomp]`.

Establish `kz : Spec.map (CommRingCat.ofHom qm) ≫ z₀ = z₁`. Rewrite using `[← cancel_mono P.ι, Category.assoc, ← h₀'.w, ← h₁.w, ← Category.assoc, kf, Category.assoc]`. Use `isIso_specMap_of_bij qm hb` as an intermediate fact. Conclude with `pbRel_isIso_of _ _ _ _ h (h₁.map sch) (h₀'.map sch) (sch.map (Spec.map (CommRingCat.ofHom qm))) (by rw [← sch.map_comp, kf, sch.map_comp]) (by rw [← sch.map_comp, kz])`.
-/
theorem LeafLocIso_of (hZ : LeafZ) (hQ : LeafQuot) : LeafLocIso := by
  intro H d P V h
  have := P.cl
  set A := Γ(P.X, V.1)
  set I := P.ι.ker.ideal V
  set φ : A →+* H.obj A I := eta H P V
  obtain ⟨⟨z₁, h₁⟩, -⟩ := hZ P.X P.Z P.ι V (H.obj A I) φ
  obtain ⟨⟨z₀, h₀'⟩, -⟩ := hZ P.X P.Z P.ι V A (RingHom.id A)
  have e₀ : Spec.map (CommRingCat.ofHom (RingHom.id A)) ≫ V.2.fromSpec = V.2.fromSpec := by simp
  rw [e₀] at h₀'
  have hle : I.map (RingHom.id A) ≤ (I.map φ).comap φ := by rw [Ideal.map_id]; exact Ideal.le_comap_map
  set qm := Ideal.quotientMap (I.map φ) φ hle
  have hb : Function.Bijective qm := quot_bij_of_eq φ I _ (Ideal.map_id I) _ rfl hle (hQ A (H.obj A I) φ I (H.ind A I))
  have hcomp : qm.comp (Ideal.Quotient.mk (I.map (RingHom.id A))) = (Ideal.Quotient.mk (I.map φ)).comp φ :=
    Ideal.quotientMap_comp_mk hle
  have kf : Spec.map (CommRingCat.ofHom qm) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (RingHom.id A)))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ))) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomp]
  have kz : Spec.map (CommRingCat.ofHom qm) ≫ z₀ = z₁ := by
    rw [← cancel_mono P.ι, Category.assoc, ← h₀'.w, ← h₁.w, ← Category.assoc, kf, Category.assoc]
  have := isIso_specMap_of_bij qm hb
  exact pbRel_isIso_of _ _ _ _ h (h₁.map sch) (h₀'.map sch) (sch.map (Spec.map (CommRingCat.ofHom qm)))
    (by rw [← sch.map_comp, kf, sch.map_comp]) (by rw [← sch.map_comp, kz])

end LateralTheory.CohomologicalPurity.TubeCut

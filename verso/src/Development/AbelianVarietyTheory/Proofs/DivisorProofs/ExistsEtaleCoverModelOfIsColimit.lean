import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleModelOfIsColimit
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtaleCoverDescent

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in

/- English proof (translation)
Establish `hP` using `isPullback_SpecMap_of_isPushout f g inl inr H`. Take `⟨w, hw, -⟩` from `Scheme.Pullback.exists_preimage_pullback x y hxy`. Use `⟨hP.isoPullback.inv w, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, hP.isoPullback_inv_fst]`. Conclude with `hw`.
-/
theorem _root_.GlobalTheory.EtaleCoverDescent.exists_point_of_isPushout {R S T P : CommRingCat.{0}} {f : R ⟶ S} {g : R ⟶ T}
    {inl : S ⟶ P} {inr : T ⟶ P} (H : IsPushout f g inl inr) (x : Spec S) (y : Spec T)
    (hxy : Spec.map f x = Spec.map g y) : ∃ z : Spec P, Spec.map inl z = x := by
  have hP := isPullback_SpecMap_of_isPushout f g inl inr H
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  refine ⟨hP.isoPullback.inv w, ?_⟩
  rw [← Scheme.Hom.comp_apply, hP.isoPullback_inv_fst]
  exact hw

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
/- English proof (translation)
Use `letI := g.hom.toAlgebra`. Use `haveI : Algebra.Etale c.pt B := hg`. Take `⟨j, A, _, _, hA, ⟨e⟩⟩` from `_root_.GlobalTheory.EtaleDescent.exists_etale_model_of_isColimit J D c hc B`. Use `letI : Algebra (D.obj j) c.pt := (c.ι.app j).hom.toAlgebra`. Use `⟨j, CommRingCat.of A, CommRingCat.ofHom (algebraMap (D.obj j) A), CommRingCat.ofHom ((e : TensorProduct (D.obj j) c.pt A →+* B).comp Algebra.TensorProduct.includeRight.toRingHom), ?_, ?_⟩` and prove the remaining obligations.

Conclude with `RingHom.etale_algebraMap.mpr hA`. Use `(CommRingCat.isPushout_tensorProduct (D.obj j) c.pt A).flip.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (RingEquiv.toCommRingCatIso e.toRingEquiv) ?_ ?_ ?_ ?_` and prove the remaining obligations. Both sides reduce to the same expression. Both sides reduce to the same expression. Use extensionality with `x`.

Both sides reduce to the same expression. Use extensionality with `x`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply]`. Conclude with `e.commutes x`.
-/
private lemma exists_etale_pushout_of_filtered_colimit (J : Type) [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (hc : IsColimit c) {B : CommRingCat.{0}}
    (g : c.pt ⟶ B) (hg : g.hom.Etale) :
    ∃ (j : J) (B' : CommRingCat.{0}) (a : D.obj j ⟶ B') (h : B' ⟶ B),
      a.hom.Etale ∧ IsPushout a (c.ι.app j) h g := by
  letI := g.hom.toAlgebra
  haveI : Algebra.Etale c.pt B := hg
  obtain ⟨j, A, _, _, hA, ⟨e⟩⟩ := _root_.GlobalTheory.EtaleDescent.exists_etale_model_of_isColimit J D c hc B
  letI : Algebra (D.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  refine ⟨j, CommRingCat.of A, CommRingCat.ofHom (algebraMap (D.obj j) A),
    CommRingCat.ofHom ((e : TensorProduct (D.obj j) c.pt A →+* B).comp
      Algebra.TensorProduct.includeRight.toRingHom), ?_, ?_⟩
  · exact RingHom.etale_algebraMap.mpr hA
  · refine (CommRingCat.isPushout_tensorProduct (D.obj j) c.pt A).flip.of_iso (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (RingEquiv.toCommRingCatIso e.toRingEquiv) ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · ext x
      rfl
    · ext x
      simp only [CommRingCat.hom_comp, RingHom.comp_apply]
      exact e.commutes x

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
/- English proof (translation)
Establish `hw : D.map f ≫ c.ι.app k' ≫ g = a ≫ h`. Rewrite using `[H.w, ← c.w f, Category.assoc]`. Use `⟨pushout (D.map f) a, pushout.inl (D.map f) a, pushout.desc (c.ι.app k' ≫ g) h hw, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `RingHom.Etale.isStableUnderBaseChange.pushout_inl RingHom.Etale.respectsIso _ _ ha`. Establish `top : IsPushout a (D.map f) (pushout.inr (D.map f) a) (pushout.inl (D.map f) a)` using `(IsPushout.of_hasPushout (D.map f) a).flip`.

Establish `big : IsPushout a (D.map f ≫ c.ι.app k') (pushout.inr (D.map f) a ≫ pushout.desc (c.ι.app k' ≫ g) h hw) g`. Rewrite using `[c.w f, pushout.inr_desc]`. Conclude with `H`. Conclude with `big.of_top (pushout.inl_desc _ _ _) top`. Introduce and unpack `p ⟨v, hv⟩`.

Take `⟨z, hz⟩` from `_root_.GlobalTheory.EtaleCoverDescent.exists_point_of_isPushout (IsPushout.of_hasPushout (D.map f) a) p v hv.symm`. Conclude with `⟨z, hz⟩`.
-/
private lemma exists_etale_pushout_at_later_index_of_range {J : Type} [SmallCategory J]
    {D : J ⥤ CommRingCat.{0}} (c : Cocone D) {k k' : J} (f : k ⟶ k') {B B' : CommRingCat.{0}}
    {g : c.pt ⟶ B} {a : D.obj k ⟶ B'} {h : B' ⟶ B} (ha : a.hom.Etale)
    (H : IsPushout a (c.ι.app k) h g) :
    ∃ (B'' : CommRingCat.{0}) (a' : D.obj k' ⟶ B'') (h' : B'' ⟶ B),
      a'.hom.Etale ∧ IsPushout a' (c.ι.app k') h' g ∧
      ∀ p : Spec (D.obj k'), Spec.map (D.map f) p ∈ Set.range (Spec.map a) →
        p ∈ Set.range (Spec.map a') := by
  have hw : D.map f ≫ c.ι.app k' ≫ g = a ≫ h := by
    rw [H.w, ← c.w f, Category.assoc]
  refine ⟨pushout (D.map f) a, pushout.inl (D.map f) a,
    pushout.desc (c.ι.app k' ≫ g) h hw, ?_, ?_, ?_⟩
  · exact RingHom.Etale.isStableUnderBaseChange.pushout_inl RingHom.Etale.respectsIso _ _ ha
  · have top : IsPushout a (D.map f) (pushout.inr (D.map f) a) (pushout.inl (D.map f) a) :=
      (IsPushout.of_hasPushout (D.map f) a).flip
    have big : IsPushout a (D.map f ≫ c.ι.app k')
        (pushout.inr (D.map f) a ≫ pushout.desc (c.ι.app k' ≫ g) h hw) g := by
      rw [c.w f, pushout.inr_desc]
      exact H
    exact big.of_top (pushout.inl_desc _ _ _) top
  · rintro p ⟨v, hv⟩
    obtain ⟨z, hz⟩ := _root_.GlobalTheory.EtaleCoverDescent.exists_point_of_isPushout (IsPushout.of_hasPushout (D.map f) a) p v hv.symm
    exact ⟨z, hz⟩

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in

/- English proof (translation)
Introduce `J _ _ D c hc ι _ B g hg hsurj j₀`. Use `Fintype.ofFinite ι` as an intermediate fact. Use `choose jm Bm am hm ham hHm using fun i => exists_etale_pushout_of_filtered_colimit J D c hc (g i) (hg i)`. Set `O : Finset J` to `insert j₀ (Finset.univ.image jm)`. Set `j1` to `IsFiltered.sup O ∅`.

Establish `f0 : j₀ ⟶ j1` using `IsFiltered.toSup O ∅ (Finset.mem_insert_self _ _)`. Establish `fm : ∀ i, jm i ⟶ j1` using `fun i => IsFiltered.toSup O ∅ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))`. Use `choose B1 a1 h1 ha1 hH1 _ using fun i => exists_etale_pushout_at_later_index_of_range c (fm i) (ham i) (hHm i)`. Set `W : Set (Spec (D.obj j1))` to `{q | ∀ i, q ∉ Set.range (Spec.map (a1 i))}`. Establish `hW : IsClosed W`.

Establish `hWe : W = (⋃ i, Set.range (Spec.map (a1 i)))ᶜ`. Use extensionality with `q`. Simplify using `[W]`. Rewrite using `[hWe, isClosed_compl_iff]`. Use `isOpen_iUnion fun i => ?_` and prove the remaining obligations.

Establish `: Etale (Spec.map (a1 i))`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Etale)]`. Conclude with `ha1 i`. Conclude with `(Spec.map (a1 i)).isOpenMap.isOpen_range`. Establish `claim : ∃ (k : J) (f : j1 ⟶ k), ∀ p : Spec (D.obj k), Spec.map (D.map f) p ∉ W`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Use `haveI : ∀ {i i' : Jᵒᵖ} (f : i ⟶ i'), IsAffineHom ((D.op ⋙ Scheme.Spec).map f) := fun f => inferInstanceAs (IsAffineHom (Spec.map (D.map f.unop)))`. Take `⟨s, hs⟩` from `exists_mem_of_isClosed_of_nonempty' (D.op ⋙ Scheme.Spec) (Scheme.Spec.mapCone c.op) (isLimitOfPreserves Scheme.Spec hc.op) (j := op j1) (fun i hij => (Spec.map (D.map hij.unop)) ⁻¹' W) (fun i hij => hW.preimage (Spec.map _).continuous) (fun i hij => hcon _ hij.unop) (fun i hij => …`. Express the relevant statement in the definitionally equal form `Spec.map (D.map hij.unop) (Spec.map (D.map hi'i.unop) x) ∈ W`.

Rewrite using `[← Scheme.Hom.comp_apply, ← Spec.map_comp, ← D.map_comp]`. Conclude with `hx)`. Establish `hs1 : Spec.map (c.ι.app j1) s ∈ W`. Use `hs (op j1) (𝟙 _)` as an intermediate fact. Express the relevant statement in the definitionally equal form `Spec.map (D.map (𝟙 j1)) (Spec.map (c.ι.app j1) s) ∈ W at this`.

Simplify `this` using `[D.map_id, Spec.map_id]`. Take `⟨i, v, rfl⟩` from `hsurj s`. Use `hs1 i ⟨Spec.map (h1 i) v, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, ← Spec.map_comp, (hH1 i).w, Spec.map_comp, Scheme.Hom.comp_apply]`. Take `⟨k, f, hk⟩` from `claim`.

Use `choose B2 a2 h2 ha2 hH2 hpt using fun i => exists_etale_pushout_at_later_index_of_range c f (ha1 i) (hH1 i)`. Use `⟨k, f0 ≫ f, B2, a2, h2, fun i => ⟨ha2 i, hH2 i⟩, fun p => ?_⟩` and prove the remaining obligations. Establish `hp` using `hk p`. Simplify using `only [W, Set.mem_setOf_eq, not_forall, not_not] at hp`. Take `⟨i, hi⟩` from `hp`.

Take `⟨v, hv⟩` from `hpt i p hi`. Conclude with `⟨i, v, hv⟩`.
-/
theorem _root_.GlobalTheory.EtaleCoverDescent.exists_etale_cover_model_of_isColimit :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (ι : Type) [Finite ι] (B : ι → CommRingCat.{0}) (g : ∀ i, c.pt ⟶ B i), (∀ i, (g i).hom.Etale) → (∀ p : Spec c.pt, ∃ i v, Spec.map (g i) v = p) → ∀ j₀ : J, ∃ (j : J) (_ : j₀ ⟶ j) (B' : ι → CommRingCat.{0}) (g' : ∀ i, D.obj j ⟶ B' i) (h : ∀ i, B' i ⟶ B i), (∀ i, (g' i).hom.Etale ∧ IsPushout (g' i) (c.ι.app j) (h i) (g i)) ∧ ∀ p : Spec (D.obj j), ∃ i v, Spec.map (g' i) v = p := by
  intro J _ _ D c hc ι _ B g hg hsurj j₀
  classical
  have := Fintype.ofFinite ι
  choose jm Bm am hm ham hHm using fun i => exists_etale_pushout_of_filtered_colimit J D c hc (g i) (hg i)
  let O : Finset J := insert j₀ (Finset.univ.image jm)
  let j1 := IsFiltered.sup O ∅
  have f0 : j₀ ⟶ j1 := IsFiltered.toSup O ∅ (Finset.mem_insert_self _ _)
  have fm : ∀ i, jm i ⟶ j1 := fun i =>
    IsFiltered.toSup O ∅ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  choose B1 a1 h1 ha1 hH1 _ using fun i => exists_etale_pushout_at_later_index_of_range c (fm i) (ham i) (hHm i)
  let W : Set (Spec (D.obj j1)) := {q | ∀ i, q ∉ Set.range (Spec.map (a1 i))}
  have hW : IsClosed W := by
    have hWe : W = (⋃ i, Set.range (Spec.map (a1 i)))ᶜ := by
      ext q
      simp [W]
    rw [hWe, isClosed_compl_iff]
    refine isOpen_iUnion fun i => ?_
    have : Etale (Spec.map (a1 i)) := by
      rw [HasRingHomProperty.Spec_iff (P := @Etale)]
      exact ha1 i
    exact (Spec.map (a1 i)).isOpenMap.isOpen_range
  have claim : ∃ (k : J) (f : j1 ⟶ k), ∀ p : Spec (D.obj k), Spec.map (D.map f) p ∉ W := by
    by_contra hcon
    push_neg at hcon
    haveI : ∀ {i i' : Jᵒᵖ} (f : i ⟶ i'), IsAffineHom ((D.op ⋙ Scheme.Spec).map f) :=
      fun f => inferInstanceAs (IsAffineHom (Spec.map (D.map f.unop)))
    obtain ⟨s, hs⟩ := exists_mem_of_isClosed_of_nonempty' (D.op ⋙ Scheme.Spec)
      (Scheme.Spec.mapCone c.op) (isLimitOfPreserves Scheme.Spec hc.op) (j := op j1)
      (fun i hij => (Spec.map (D.map hij.unop)) ⁻¹' W)
      (fun i hij => hW.preimage (Spec.map _).continuous)
      (fun i hij => hcon _ hij.unop)
      (fun i hij => (hW.preimage (Spec.map _).continuous).isCompact)
      (fun i i' hi'i hij x hx => by
        change Spec.map (D.map hij.unop) (Spec.map (D.map hi'i.unop) x) ∈ W
        rw [← Scheme.Hom.comp_apply, ← Spec.map_comp, ← D.map_comp]
        exact hx)
    have hs1 : Spec.map (c.ι.app j1) s ∈ W := by
      have := hs (op j1) (𝟙 _)
      change Spec.map (D.map (𝟙 j1)) (Spec.map (c.ι.app j1) s) ∈ W at this
      simpa [D.map_id, Spec.map_id] using this
    obtain ⟨i, v, rfl⟩ := hsurj s
    refine hs1 i ⟨Spec.map (h1 i) v, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Spec.map_comp, (hH1 i).w, Spec.map_comp, Scheme.Hom.comp_apply]
  obtain ⟨k, f, hk⟩ := claim
  choose B2 a2 h2 ha2 hH2 hpt using fun i => exists_etale_pushout_at_later_index_of_range c f (ha1 i) (hH1 i)
  refine ⟨k, f0 ≫ f, B2, a2, h2, fun i => ⟨ha2 i, hH2 i⟩, fun p => ?_⟩
  have hp := hk p
  simp only [W, Set.mem_setOf_eq, not_forall, not_not] at hp
  obtain ⟨i, hi⟩ := hp
  obtain ⟨v, hv⟩ := hpt i p hi
  exact ⟨i, v, hv⟩

end GlobalTheory.EtaleCoverDescent

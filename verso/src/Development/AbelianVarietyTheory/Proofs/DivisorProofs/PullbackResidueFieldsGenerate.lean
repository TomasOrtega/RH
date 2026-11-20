import Mathlib
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory

open CategoryTheory Limits AlgebraicGeometry in

/- English proof (translation)
Take `⟨⟨x, φ⟩, rfl⟩` from `(Scheme.SpecToEquivOfField K Z).symm.surjective m`. Simplify using `only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk] at hm`. Establish `hx : x = t`. Establish `h` using `congr($hm (IsLocalRing.closedPoint _))`. Establish `e₁` using `Scheme.fromSpecResidueField_apply x (Spec.map φ (Spec.map (CommRingCat.ofHom K.subtype) (IsLocalRing.closedPoint _)))`.

Establish `e₂` using `Scheme.fromSpecResidueField_apply t (IsLocalRing.closedPoint _)`. Conclude with `e₁.symm.trans (h.trans e₂)`. Substitute `hx` using the available equality. Rewrite `hm` using `[← Category.assoc, ← Spec.map_comp]`. Establish `hφ : φ ≫ CommRingCat.ofHom K.subtype = 𝟙 _`.

Rewrite using `[← Spec.map_inj, Spec.map_id, ← cancel_mono (Z.fromSpecResidueField x), hm]`. Conclude with `(Category.id_comp _).symm`. Rewrite using `[eq_top_iff]`. Introduce `y _`. Establish `hy : K.subtype (φ.hom y) = y` using `congr($hφ y)`.

Rewrite using `[← hy]`. Conclude with `(φ.hom y).2`.
-/
theorem _root_.GlobalTheory.subfield_eq_top_of_fromSpecResidueField_factors (Z : Scheme.{0}) (t : Z)
    (K : Subfield (Z.residueField t)) (m : Spec (CommRingCat.of K) ⟶ Z)
    (hm : Spec.map (CommRingCat.ofHom K.subtype) ≫ m = Z.fromSpecResidueField t) : K = ⊤ := by
  obtain ⟨⟨x, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Z).symm.surjective m
  simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk] at hm
  have hx : x = t := by
    have h := congr($hm (IsLocalRing.closedPoint _))
    have e₁ := Scheme.fromSpecResidueField_apply x
      (Spec.map φ (Spec.map (CommRingCat.ofHom K.subtype) (IsLocalRing.closedPoint _)))
    have e₂ := Scheme.fromSpecResidueField_apply t (IsLocalRing.closedPoint _)
    exact e₁.symm.trans (h.trans e₂)
  subst hx
  rw [← Category.assoc, ← Spec.map_comp] at hm
  have hφ : φ ≫ CommRingCat.ofHom K.subtype = 𝟙 _ := by
    rw [← Spec.map_inj, Spec.map_id, ← cancel_mono (Z.fromSpecResidueField x), hm]
    exact (Category.id_comp _).symm
  rw [eq_top_iff]
  intro y _
  have hy : K.subtype (φ.hom y) = y := congr($hφ y)
  rw [← hy]
  exact (φ.hom y).2

open CategoryTheory Limits AlgebraicGeometry in

/- English proof (translation)
Use `set L := Subfield.closure (Set.range ((pullback.fst f g).residueFieldMap t).hom ∪ Set.range ((pullback.snd f g).residueFieldMap t).hom)`. Set `ι : CommRingCat.of L ⟶ (pullback f g).residueField t` to `CommRingCat.ofHom L.subtype`. Set `cx : X.residueField (pullback.fst f g t) ⟶ CommRingCat.of L` to `CommRingCat.ofHom (((pullback.fst f g).residueFieldMap t).hom.codRestrict L fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩))`. Set `cy : Y.residueField (pullback.snd f g t) ⟶ CommRingCat.of L` to `CommRingCat.ofHom (((pullback.snd f g).residueFieldMap t).hom.codRestrict L fun a => Subfield.subset_closure (Or.inr ⟨a, rfl⟩))`. Establish `hcx : cx ≫ ι = (pullback.fst f g).residueFieldMap t` using `rfl`.

Establish `hcy : cy ≫ ι = (pullback.snd f g).residueFieldMap t` using `rfl`. Establish `hι : Mono ι` using `ConcreteCategory.mono_of_injective _ Subtype.val_injective`. Establish `e : f (pullback.fst f g t) = g (pullback.snd f g t)`. Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]`. Establish `key : f.residueFieldMap (pullback.fst f g t) ≫ cx = (S.residueFieldCongr e).hom ≫ g.residueFieldMap (pullback.snd f g t) ≫ cy`.

Rewrite using `[← cancel_mono ι]`. Simplify using `only [Category.assoc, hcx, hcy]`. Rewrite using `[← Scheme.residueFieldMap_comp, ← Scheme.residueFieldMap_comp]`. Conclude with `Scheme.Hom.residueFieldMap_congr pullback.condition t`. Establish `hab : (Spec.map cx ≫ X.fromSpecResidueField (pullback.fst f g t)) ≫ f = (Spec.map cy ≫ Y.fromSpecResidueField (pullback.snd f g t)) ≫ g`.

Rewrite using `[Category.assoc, Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, key, Spec.map_comp_assoc, Spec.map_comp_assoc, Scheme.residueFieldCongr_fromSpe …`. Rewrite using `[Spec.map_comp_assoc]`. Establish `hm : Spec.map (CommRingCat.ofHom L.subtype) ≫ pullback.lift _ _ hab = (pullback f g).fromSpecResidueField t`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, pullback.lift_fst, ← Spec.map_comp_assoc]`.

Conclude with `Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ t`. Rewrite using `[Category.assoc, pullback.lift_snd, ← Spec.map_comp_assoc]`. Conclude with `Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ t`. Conclude with `_root_.GlobalTheory.subfield_eq_top_of_fromSpecResidueField_factors _ t L _ hm`.
-/
theorem _root_.GlobalTheory.closure_range_residueFieldMap_pullback_eq_top (X Y S : Scheme.{0}) (f : X ⟶ S) (g : Y ⟶ S)
    (t : ↑(pullback f g)) :
    Subfield.closure (Set.range ((pullback.fst f g).residueFieldMap t).hom ∪
      Set.range ((pullback.snd f g).residueFieldMap t).hom) = ⊤ := by
  set L := Subfield.closure (Set.range ((pullback.fst f g).residueFieldMap t).hom ∪
      Set.range ((pullback.snd f g).residueFieldMap t).hom)
  let ι : CommRingCat.of L ⟶ (pullback f g).residueField t := CommRingCat.ofHom L.subtype
  let cx : X.residueField (pullback.fst f g t) ⟶ CommRingCat.of L := CommRingCat.ofHom
    (((pullback.fst f g).residueFieldMap t).hom.codRestrict L
      fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
  let cy : Y.residueField (pullback.snd f g t) ⟶ CommRingCat.of L := CommRingCat.ofHom
    (((pullback.snd f g).residueFieldMap t).hom.codRestrict L
      fun a => Subfield.subset_closure (Or.inr ⟨a, rfl⟩))
  have hcx : cx ≫ ι = (pullback.fst f g).residueFieldMap t := rfl
  have hcy : cy ≫ ι = (pullback.snd f g).residueFieldMap t := rfl
  have hι : Mono ι := ConcreteCategory.mono_of_injective _ Subtype.val_injective
  have e : f (pullback.fst f g t) = g (pullback.snd f g t) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have key : f.residueFieldMap (pullback.fst f g t) ≫ cx =
      (S.residueFieldCongr e).hom ≫ g.residueFieldMap (pullback.snd f g t) ≫ cy := by
    rw [← cancel_mono ι]
    simp only [Category.assoc, hcx, hcy]
    rw [← Scheme.residueFieldMap_comp, ← Scheme.residueFieldMap_comp]
    exact Scheme.Hom.residueFieldMap_congr pullback.condition t
  have hab : (Spec.map cx ≫ X.fromSpecResidueField (pullback.fst f g t)) ≫ f =
      (Spec.map cy ≫ Y.fromSpecResidueField (pullback.snd f g t)) ≫ g := by
    rw [Category.assoc, Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f,
      ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc, key, Spec.map_comp_assoc, Spec.map_comp_assoc,
      Scheme.residueFieldCongr_fromSpecResidueField]
    rw [Spec.map_comp_assoc]
  have hm : Spec.map (CommRingCat.ofHom L.subtype) ≫ pullback.lift _ _ hab =
      (pullback f g).fromSpecResidueField t := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Spec.map_comp_assoc]
      exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ t
    · rw [Category.assoc, pullback.lift_snd, ← Spec.map_comp_assoc]
      exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ t
  exact _root_.GlobalTheory.subfield_eq_top_of_fromSpecResidueField_factors _ t L _ hm

end GlobalTheory

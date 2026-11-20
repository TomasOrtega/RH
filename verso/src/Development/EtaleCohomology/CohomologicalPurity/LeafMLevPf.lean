import Development.EtaleCohomology.CohomologicalPurity.LeafExcLevelPf

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

abbrev levF (n : SimplexCategoryᵒᵖ) : Spc ⥤ Spc := (evaluation SimplexCategoryᵒᵖ PSh).obj n ⋙ disc

/- English proof (translation)
Introduce `P' P φ n`. Set `F` to `levF n`. Establish `hc : F.map (P'.hom ≫ φ.right) = F.map P'.hom ≫ F.map φ.right` using `F.map_comp _ _`. Set `a : disc.obj ((MM φ).obj n) ≅ MM ((lev n).map φ)` to `(PreservesPushout.iso F P'.hom (P'.hom ≫ φ.right)).symm ≪≫ pushout.congrHom rfl hc`. Set `b : disc.obj ((dbl P).obj n) ≅ dbl ((lev n).obj P)` to `(PreservesPushout.iso F P.hom P.hom).symm`.

Use `⟨a, b, ?_⟩` and prove the remaining obligations. Rewrite using `[← Iso.inv_comp_eq]`. Express the relevant statement in the definitionally equal form `(pushout.congrHom rfl hc).inv ≫ (PreservesPushout.iso F P'.hom (P'.hom ≫ φ.right)).hom ≫ F.map (gM φ) ≫ (PreservesPushout.iso F P.hom P.hom).inv = gM ((lev n).map φ)`. Apply `pushout.hom_ext` to reduce the goal to its premises. Rewrite using `[pushout.congrHom_inv, pushout.inl_desc_assoc, Category.id_comp] erw [PreservesPushout.inl_iso_hom_assoc, ← F.map_comp_assoc, pushout.inl_desc, pushout.inl_desc, F.map_comp_assoc] erw [PreservesPushout.inl_iso_inv]`.

Both sides reduce to the same expression. Rewrite using `[pushout.congrHom_inv, pushout.inr_desc_assoc, Category.id_comp] erw [PreservesPushout.inr_iso_hom_assoc, ← F.map_comp_assoc, pushout.inr_desc, pushout.inr_desc] erw [PreservesPushout.inr_iso_inv]`. Both sides reduce to the same expression.
-/
theorem LeafMLev_of : LeafMLev := by
  intro P' P φ n
  let F := levF n
  have hc : F.map (P'.hom ≫ φ.right) = F.map P'.hom ≫ F.map φ.right := F.map_comp _ _
  let a : disc.obj ((MM φ).obj n) ≅ MM ((lev n).map φ) :=
    (PreservesPushout.iso F P'.hom (P'.hom ≫ φ.right)).symm ≪≫ pushout.congrHom rfl hc
  let b : disc.obj ((dbl P).obj n) ≅ dbl ((lev n).obj P) :=
    (PreservesPushout.iso F P.hom P.hom).symm
  refine ⟨a, b, ?_⟩
  rw [← Iso.inv_comp_eq]
  change (pushout.congrHom rfl hc).inv ≫ (PreservesPushout.iso F P'.hom (P'.hom ≫ φ.right)).hom ≫ F.map (gM φ) ≫
    (PreservesPushout.iso F P.hom P.hom).inv = gM ((lev n).map φ)
  apply pushout.hom_ext
  · rw [pushout.congrHom_inv, pushout.inl_desc_assoc, Category.id_comp]
    erw [PreservesPushout.inl_iso_hom_assoc, ← F.map_comp_assoc, pushout.inl_desc, pushout.inl_desc, F.map_comp_assoc]
    erw [PreservesPushout.inl_iso_inv]
    rfl
  · rw [pushout.congrHom_inv, pushout.inr_desc_assoc, Category.id_comp]
    erw [PreservesPushout.inr_iso_hom_assoc, ← F.map_comp_assoc, pushout.inr_desc, pushout.inr_desc]
    erw [PreservesPushout.inr_iso_inv]
    rfl

end LateralTheory.CohomologicalPurity.TubeCut

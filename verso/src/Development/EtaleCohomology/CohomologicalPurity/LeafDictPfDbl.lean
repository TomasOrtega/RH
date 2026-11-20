import Development.EtaleCohomology.CohomologicalPurity.LeafDictPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.DictPf

/- English proof (translation)
Use `⟨fun U => (PreservesPushout.iso disc (yoneda.map U.ι) (yoneda.map U.ι)).symm, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `X U`. Conclude with `PreservesPushout.inl_iso_inv disc _ _`. Introduce `X U`. Conclude with `PreservesPushout.inr_iso_inv disc _ _`.

Introduce `X' X f U' U h dsimp only`. Use `(Iso.inv_comp_eq _).1 ?_` and prove the remaining obligations. Apply `pushout.hom_ext` to reduce the goal to its premises. Establish `a1 : pushout.inl (opn U').hom (opn U').hom ≫ (PreservesPushout.iso disc (yoneda.map U'.ι) (yoneda.map U'.ι)).hom = disc.map (pushout.inl _ _)` using `PreservesPushout.inl_iso_hom disc _ _`. Establish `a2 : disc.map (pushout.inl (yoneda.map U.ι) (yoneda.map U.ι)) ≫ (PreservesPushout.iso disc (yoneda.map U.ι) (yoneda.map U.ι)).symm.hom = pushout.inl (opn U).hom (opn U).hom` using `PreservesPushout.inl_iso_inv disc _ _`.

Establish `il : pushout.inl _ _ ≫ Qmap f U' U h = yoneda.map f ≫ pushout.inl _ _` using `pushout.inl_desc _ _ _`. Use `show pushout.inl (opn U').hom (opn U').hom ≫ (PreservesPushout.iso disc (yoneda.map U'.ι) (yoneda.map U'.ι)).hom ≫ disc.map (Qmap f U' U h) ≫ (PreservesPushout.iso disc (yoneda.map U.ι) (yoneda.map U.ι)).symm.hom = _`. Use `erw [← Category.assoc, a1, ← Category.assoc, ← Functor.map_comp, il, Functor.map_comp, Category.assoc, a2]`. Conclude with `(pushout.inl_desc _ _ _).symm`. Establish `a1 : pushout.inr (opn U').hom (opn U').hom ≫ (PreservesPushout.iso disc (yoneda.map U'.ι) (yoneda.map U'.ι)).hom = disc.map (pushout.inr _ _)` using `PreservesPushout.inr_iso_hom disc _ _`.

Establish `a2 : disc.map (pushout.inr (yoneda.map U.ι) (yoneda.map U.ι)) ≫ (PreservesPushout.iso disc (yoneda.map U.ι) (yoneda.map U.ι)).symm.hom = pushout.inr (opn U).hom (opn U).hom` using `PreservesPushout.inr_iso_inv disc _ _`. Establish `il : pushout.inr _ _ ≫ Qmap f U' U h = yoneda.map f ≫ pushout.inr _ _` using `pushout.inr_desc _ _ _`. Use `show pushout.inr (opn U').hom (opn U').hom ≫ (PreservesPushout.iso disc (yoneda.map U'.ι) (yoneda.map U'.ι)).hom ≫ disc.map (Qmap f U' U h) ≫ (PreservesPushout.iso disc (yoneda.map U.ι) (yoneda.map U.ι)).symm.hom = _`. Use `erw [← Category.assoc, a1, ← Category.assoc, ← Functor.map_comp, il, Functor.map_comp, Category.assoc, a2]`. Conclude with `(pushout.inr_desc _ _ _).symm`.
-/
theorem LeafDbl_pf : LeafDbl := by
  refine ⟨fun U => (PreservesPushout.iso disc (yoneda.map U.ι) (yoneda.map U.ι)).symm, ?_, ?_, ?_⟩
  · intro X U
    exact PreservesPushout.inl_iso_inv disc _ _
  · intro X U
    exact PreservesPushout.inr_iso_inv disc _ _
  · intro X' X f U' U h
    dsimp only
    refine (Iso.inv_comp_eq _).1 ?_
    apply pushout.hom_ext
    · have a1 : pushout.inl (opn U').hom (opn U').hom ≫ (PreservesPushout.iso disc (yoneda.map U'.ι) (yoneda.map U'.ι)).hom =
          disc.map (pushout.inl _ _) := PreservesPushout.inl_iso_hom disc _ _
      have a2 : disc.map (pushout.inl (yoneda.map U.ι) (yoneda.map U.ι)) ≫
          (PreservesPushout.iso disc (yoneda.map U.ι) (yoneda.map U.ι)).symm.hom = pushout.inl (opn U).hom (opn U).hom :=
        PreservesPushout.inl_iso_inv disc _ _
      have il : pushout.inl _ _ ≫ Qmap f U' U h = yoneda.map f ≫ pushout.inl _ _ := pushout.inl_desc _ _ _
      show pushout.inl (opn U').hom (opn U').hom ≫ (PreservesPushout.iso disc (yoneda.map U'.ι) (yoneda.map U'.ι)).hom ≫
        disc.map (Qmap f U' U h) ≫ (PreservesPushout.iso disc (yoneda.map U.ι) (yoneda.map U.ι)).symm.hom = _
      erw [← Category.assoc, a1, ← Category.assoc, ← Functor.map_comp, il, Functor.map_comp, Category.assoc, a2]
      exact (pushout.inl_desc _ _ _).symm
    · have a1 : pushout.inr (opn U').hom (opn U').hom ≫ (PreservesPushout.iso disc (yoneda.map U'.ι) (yoneda.map U'.ι)).hom =
          disc.map (pushout.inr _ _) := PreservesPushout.inr_iso_hom disc _ _
      have a2 : disc.map (pushout.inr (yoneda.map U.ι) (yoneda.map U.ι)) ≫
          (PreservesPushout.iso disc (yoneda.map U.ι) (yoneda.map U.ι)).symm.hom = pushout.inr (opn U).hom (opn U).hom :=
        PreservesPushout.inr_iso_inv disc _ _
      have il : pushout.inr _ _ ≫ Qmap f U' U h = yoneda.map f ≫ pushout.inr _ _ := pushout.inr_desc _ _ _
      show pushout.inr (opn U').hom (opn U').hom ≫ (PreservesPushout.iso disc (yoneda.map U'.ι) (yoneda.map U'.ι)).hom ≫
        disc.map (Qmap f U' U h) ≫ (PreservesPushout.iso disc (yoneda.map U.ι) (yoneda.map U.ι)).symm.hom = _
      erw [← Category.assoc, a1, ← Category.assoc, ← Functor.map_comp, il, Functor.map_comp, Category.assoc, a2]
      exact (pushout.inr_desc _ _ _).symm

/- English proof (translation)
The claim follows from `LeafDict_of hD hE hP LeafDbl_pf`.
-/
theorem LeafDict_of' (hD : Cl.LeafDisc) (hE : LeafEv) (hP : LeafPair) : Cl.LeafDict := LeafDict_of hD hE hP LeafDbl_pf

end LateralTheory.CohomologicalPurity.DictPf

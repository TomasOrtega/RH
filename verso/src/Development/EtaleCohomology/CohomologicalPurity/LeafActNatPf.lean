import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

/- English proof (translation)
Apply `pushout.hom_ext` to reduce the goal to its premises. Simplify using `only [dbl.map, dbl.fold, pushout.map] erw [pushout.inl_desc_assoc, Category.assoc, pushout.inl_desc, pushout.inl_desc_assoc]`. Simplify using the standard rewrite rules. Simplify using `only [dbl.map, dbl.fold, pushout.map] erw [pushout.inr_desc_assoc, Category.assoc, pushout.inr_desc, pushout.inr_desc_assoc]`. Simplify using the standard rewrite rules.
-/
theorem dbl_map_fold {P' P : Arrow Spc} (φ : P' ⟶ P) :
    dbl.map φ ≫ dbl.fold P = dbl.fold P' ≫ φ.right := by
  apply pushout.hom_ext
  · simp only [dbl.map, dbl.fold, pushout.map]
    erw [pushout.inl_desc_assoc, Category.assoc, pushout.inl_desc, pushout.inl_desc_assoc]
    simp
  · simp only [dbl.map, dbl.fold, pushout.map]
    erw [pushout.inr_desc_assoc, Category.assoc, pushout.inr_desc, pushout.inr_desc_assoc]
    simp

/- English proof (translation)
Introduce `hA q _ P' P φ n m i j a b`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `hc` using `(hA q).1 (dbl.map φ) (pull _ (dbl.fold P) (tw q i) n a) b.1`. Express the relevant statement in the definitionally equal form `pull _ (dbl.map φ) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1 - pull _ (dbl.fold P) _ _ (pull _ (dbl.inr P) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1))) = cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ _ a)) (pull _ (dbl.map φ) _ _ b.1) - pull _ (dbl.fold P') _ _ (pull _ (dbl …`. Establish `e1 : pull (ZMod q) (dbl.map φ) (tw q i) n (pull _ (dbl.fold P) _ n a) = pull _ (dbl.fold P') _ n (pull _ φ.right _ _ a)`.

Rewrite using `[← pull_comp, ← pull_comp, dbl_map_fold]`. Establish `hcc : pull (ZMod q) (dbl.map φ) (tw q (i + j)) (n + m) (cup q (pull _ (dbl.fold P) _ n a) b.1) = cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ _ a)) (pull _ (dbl.map φ) _ _ b.1)`. Rewrite using `[hc, e1]`. Rewrite using `[map_sub, hcc]`. Use `congr 1`.

Rewrite using `[← hcc, ← pull_comp _ (dbl.map φ) (dbl.fold P), dbl_map_fold, pull_comp _ (dbl.fold P') φ.right, ← pull_comp _ φ.right (dbl.inr P), ← dbl.inr_map, pull_comp _ (dbl.inr P') (dbl.map φ)]`.
-/
theorem LeafActNat_of : LeafActNat := by
  intro hA q _ P' P φ n m i j a b
  apply Subtype.ext
  have hc := (hA q).1 (dbl.map φ) (pull _ (dbl.fold P) (tw q i) n a) b.1
  change pull _ (dbl.map φ) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1 -
      pull _ (dbl.fold P) _ _ (pull _ (dbl.inr P) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1))) =
    cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ _ a)) (pull _ (dbl.map φ) _ _ b.1) -
      pull _ (dbl.fold P') _ _ (pull _ (dbl.inr P') _ _
        (cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ _ a)) (pull _ (dbl.map φ) _ _ b.1)))
  have e1 : pull (ZMod q) (dbl.map φ) (tw q i) n (pull _ (dbl.fold P) _ n a) =
      pull _ (dbl.fold P') _ n (pull _ φ.right _ _ a) := by
    rw [← pull_comp, ← pull_comp, dbl_map_fold]
  have hcc : pull (ZMod q) (dbl.map φ) (tw q (i + j)) (n + m) (cup q (pull _ (dbl.fold P) _ n a) b.1) =
      cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ _ a)) (pull _ (dbl.map φ) _ _ b.1) := by
    rw [hc, e1]
  rw [map_sub, hcc]
  congr 1
  rw [← hcc, ← pull_comp _ (dbl.map φ) (dbl.fold P), dbl_map_fold, pull_comp _ (dbl.fold P') φ.right,
    ← pull_comp _ φ.right (dbl.inr P), ← dbl.inr_map, pull_comp _ (dbl.inr P') (dbl.map φ)]

end LateralTheory.CohomologicalPurity.TubeCut

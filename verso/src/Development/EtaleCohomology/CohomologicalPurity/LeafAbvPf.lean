import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

instance sch_preservesLimits : PreservesLimitsOfSize.{0, 0} sch := by
  unfold sch
  infer_instance

/- English proof (translation)
The claim follows from `h.map sch`.
-/
theorem sch_isPullback {P X Y Z : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) : IsPullback (sch.map fst) (sch.map snd) (sch.map f) (sch.map g) :=
  h.map sch

/- English proof (translation)
Rewrite using `[Scheme.Hom.resLE_eq_morphismRestrict]`. Conclude with `(isPullback_morphismRestrict w U).flip`.
-/
theorem isPullback_resLE {Y X : Scheme.{0}} (w : Y ⟶ X) (U : X.Opens) :
    IsPullback (w ⁻¹ᵁ U).ι (w.resLE U (w ⁻¹ᵁ U) le_rfl) w U.ι := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact (isPullback_morphismRestrict w U).flip

/- English proof (translation)
Introduce `Y X w U' U h`. Substitute `h` using the available equality. Establish `hP` using `sch_isPullback (isPullback_resLE w U)`. Use `⟨Arrow.isoMk hP.isoPullback (Iso.refl _) ?_, rfl, ?_⟩` and prove the remaining obligations. Simplify using `[opn, abv]`.

Apply `Arrow.hom_ext` to reduce the goal to its premises. Rewrite using `[Arrow.comp_left]`. Conclude with `hP.isoPullback_hom_snd`. Rewrite using `[Arrow.comp_right]`. Conclude with `Category.id_comp _`.
-/
theorem LeafAbv_of : LeafAbv := by
  intro Y X w U' U h
  subst h
  have hP := sch_isPullback (isPullback_resLE w U)
  refine ⟨Arrow.isoMk hP.isoPullback (Iso.refl _) ?_, rfl, ?_⟩
  · simp [opn, abv]
  · apply Arrow.hom_ext
    · rw [Arrow.comp_left]
      exact hP.isoPullback_hom_snd
    · rw [Arrow.comp_right]
      exact Category.id_comp _

end LateralTheory.CohomologicalPurity.TubeCut

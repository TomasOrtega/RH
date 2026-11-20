import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.TowerRallisLemma

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

/- English proof (translation)
Establish `hw : Model.genMap p₁ h₁ ≫ M.q = Model.genMap p₂ h₂ ≫ M.q`. Rewrite using `[Model.genMap_q, Model.genMap_q]`. Establish `hc : pullback.fst M.p (Spec.map (CommRingCat.ofHom (OK l K).subtype)) ≫ M.p = M.q ≫ Spec.map (CommRingCat.ofHom (OK l K).subtype)` using `pullback.condition`. Establish `g1 : ∀ {u : P.X ⟶ M.X} (hu : u ≫ M.p = P.p), Model.genMap u hu ≫ pullback.fst M.p (Spec.map (CommRingCat.ofHom (OK l K).subtype)) = pullback.fst P.p (Spec.map (CommRingCat.ofHom (OK l K).subtype)) ≫ u` using `fun hu => by`. Unfold `Model.genMap`.

Conclude with `pullback.lift_fst _ _ _`. Establish `g2 : ∀ {u : P.X ⟶ M.X} (hu : u ≫ M.p = P.p), Model.genMap u hu ≫ pullback.snd M.p (Spec.map (CommRingCat.ofHom (OK l K).subtype)) = pullback.snd P.p (Spec.map (CommRingCat.ofHom (OK l K).subtype))` using `fun hu => Model.genMap_q _ hu`. Use `IsPullback.of_isLimit (c := PullbackCone.mk _ _ hw) ?_` and prove the remaining obligations. Use `PullbackCone.IsLimit.mk hw (fun s => pullback.lift (hP.lift (s.fst ≫ pullback.fst _ _) (s.snd ≫ pullback.fst _ _) (by` and prove the remaining obligations. Simplify using `only [Category.assoc, hc]`.

Rewrite using `[reassoc_of% s.condition]))`. Use the proof step `(s.fst ≫ M.q) (by`. Rewrite using `[← h₁]`. Simplify using `only [← Category.assoc, hP.lift_fst]`. Simplify using `only [Category.assoc, hc]))`.

Use the proof step `(fun s => by`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [Category.assoc, g1 h₁, pullback.lift_fst_assoc, hP.lift_fst]`. Simplify using `only [Category.assoc, g2 h₁, pullback.lift_snd])`. Use the proof step `(fun s => by`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [Category.assoc, g1 h₂, pullback.lift_fst_assoc, hP.lift_snd]`. Simplify using `only [Category.assoc, g2 h₂, pullback.lift_snd]`. Conclude with `s.condition)`. Use the proof step `(fun s m hm₁ hm₂ => by`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[pullback.lift_fst]`. Apply `hP.hom_ext` to reduce the goal to its premises. Rewrite using `[hP.lift_fst, Category.assoc, ← g1 h₁, ← Category.assoc, hm₁]`. Rewrite using `[hP.lift_snd, Category.assoc, ← g1 h₂, ← Category.assoc, hm₂]`.

Rewrite using `[pullback.lift_snd, ← hm₁, Category.assoc, g2 h₁])`.
-/
theorem gen_pb {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M P : Model l K} (p₁ p₂ : P.X ⟶ M.X) (h₁ : p₁ ≫ M.p = P.p) (h₂ : p₂ ≫ M.p = P.p) (hP : IsPullback p₁ p₂ M.p M.p) : IsPullback (Model.genMap p₁ h₁) (Model.genMap p₂ h₂) M.q M.q := by
  have hw : Model.genMap p₁ h₁ ≫ M.q = Model.genMap p₂ h₂ ≫ M.q := by
    rw [Model.genMap_q, Model.genMap_q]
  have hc : pullback.fst M.p (Spec.map (CommRingCat.ofHom (OK l K).subtype)) ≫ M.p =
      M.q ≫ Spec.map (CommRingCat.ofHom (OK l K).subtype) := pullback.condition
  have g1 : ∀ {u : P.X ⟶ M.X} (hu : u ≫ M.p = P.p),
      Model.genMap u hu ≫ pullback.fst M.p (Spec.map (CommRingCat.ofHom (OK l K).subtype)) =
        pullback.fst P.p (Spec.map (CommRingCat.ofHom (OK l K).subtype)) ≫ u := fun hu => by
    unfold Model.genMap
    exact pullback.lift_fst _ _ _
  have g2 : ∀ {u : P.X ⟶ M.X} (hu : u ≫ M.p = P.p),
      Model.genMap u hu ≫ pullback.snd M.p (Spec.map (CommRingCat.ofHom (OK l K).subtype)) =
        pullback.snd P.p (Spec.map (CommRingCat.ofHom (OK l K).subtype)) := fun hu =>
    Model.genMap_q _ hu
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ hw) ?_
  refine PullbackCone.IsLimit.mk hw
    (fun s => pullback.lift
      (hP.lift (s.fst ≫ pullback.fst _ _) (s.snd ≫ pullback.fst _ _) (by
        simp only [Category.assoc, hc]
        rw [reassoc_of% s.condition]))
      (s.fst ≫ M.q) (by
        rw [← h₁]
        simp only [← Category.assoc, hP.lift_fst]
        simp only [Category.assoc, hc]))
    (fun s => by
      apply pullback.hom_ext
      · simp only [Category.assoc, g1 h₁, pullback.lift_fst_assoc, hP.lift_fst]
      · simp only [Category.assoc, g2 h₁, pullback.lift_snd])
    (fun s => by
      apply pullback.hom_ext
      · simp only [Category.assoc, g1 h₂, pullback.lift_fst_assoc, hP.lift_snd]
      · simp only [Category.assoc, g2 h₂, pullback.lift_snd]
        exact s.condition)
    (fun s m hm₁ hm₂ => by
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        apply hP.hom_ext
        · rw [hP.lift_fst, Category.assoc, ← g1 h₁, ← Category.assoc, hm₁]
        · rw [hP.lift_snd, Category.assoc, ← g1 h₂, ← Category.assoc, hm₂]
      · rw [pullback.lift_snd, ← hm₁, Category.assoc, g2 h₁])

end CrystallineSemistableComparison.Onto

end

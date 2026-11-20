import Development.EtaleCohomology.EtaleSheaves.SpreadingOutQuasiFiniteness

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.LocallyQuasiFiniteGraphSpreadingOut

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem toR_sk {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) :
    toR R ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
  rw [← Spec.map_comp]; rfl

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem incl_sk {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R') :
    incl hR ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = Spec.map (CommRingCat.ofHom (algebraMap k R')) := by
  rw [← Spec.map_comp]; rfl

abbrev cmp {A B K X : Scheme.{0}} (p : X ⟶ K) (a : A ⟶ B) (b : B ⟶ K) (c : A ⟶ K) (h : a ≫ b = c) :
    pullback c p ⟶ pullback b p :=
  pullback.lift (pullback.fst c p ≫ a) (pullback.snd _ _)
    (by rw [Category.assoc, h]; exact pullback.condition)

/- English proof (translation)
Substitute `h` using the available equality. Use `IsPullback.of_right (h₁₂ := pullback.snd b p) (v₁₃ := p) (h₂₂ := b) ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback b p).flip` and prove the remaining obligations. Rewrite using `[pullback.lift_snd]`. Conclude with `(IsPullback.of_hasPullback (a ≫ b) p).flip`.
-/
theorem paste {A B K X : Scheme.{0}} (p : X ⟶ K) (a : A ⟶ B) (b : B ⟶ K) (c : A ⟶ K) (h : a ≫ b = c) :
    IsPullback (cmp p a b c h) (pullback.fst c p) (pullback.fst b p) a := by
  subst h
  refine IsPullback.of_right (h₁₂ := pullback.snd b p) (v₁₃ := p) (h₂₂ := b) ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback b p).flip
  rw [pullback.lift_snd]; exact (IsPullback.of_hasPullback (a ≫ b) p).flip

/- English proof (translation)
Introduce `k _ X p _ Ω _ _ R hRfg C0 D0 c0 q v0 f e he hf hq hpb hve hlqf`. Establish `hLFT : LocallyOfFinitePresentation (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R))) p)` using `by infer_instance`. Take `⟨S, hRS, hSfg, hS⟩` from `hM k Ω R hRfg (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p) (pullback.lift c0 e he.symm) (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R))) p) (pullback.lift q f hf.symm) v0 (cmp p (toR R) _ _ (toR_sk R)) ⟨hLFT, inferInstance, inferInstance⟩ (by rw [ …`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]`.

Conclude with `hpb.w.symm`. Simplify using `only [Category.assoc, pullback.lift_snd]`. Conclude with `hve.symm) hlqf`. Use `⟨S, hRS, hSfg, fun R' hSR' hR E0 q' r hr hf' => ?_⟩` and prove the remaining obligations. Use `hS R' hSR' hR E0 _ (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R'))) p) (pullback.lift q' (r ≫ f) hf'.symm) r (cmp p (incl hR) _ _ (incl_sk hR)) (paste p _ _ _ (incl_sk hR)) (by rw [pullback.lift_fst, pullback.lift_fst]; exact hr) ?_` and prove the remaining obligations.

Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]`. Conclude with `hr.w.symm`. Simplify using `only [Category.assoc, pullback.lift_snd]`.
-/
theorem LeafSpreadLQFGraph_of (hM : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFMap) :
    LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFGraph := by
  intro k _ X p _ Ω _ _ R hRfg C0 D0 c0 q v0 f e he hf hq hpb hve hlqf
  have hLFT : LocallyOfFinitePresentation (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R))) p) := by
    infer_instance
  obtain ⟨S, hRS, hSfg, hS⟩ := hM k Ω R hRfg
    (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p) (pullback.lift c0 e he.symm)
    (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R))) p) (pullback.lift q f hf.symm) v0
    (cmp p (toR R) _ _ (toR_sk R))
    ⟨hLFT, inferInstance, inferInstance⟩ (by rw [pullback.lift_fst]; exact hq) (paste p _ _ _ (toR_sk R))
    (by rw [pullback.lift_fst, pullback.lift_fst]; exact hpb) (by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]; exact hpb.w.symm
      · simp only [Category.assoc, pullback.lift_snd]; exact hve.symm) hlqf
  refine ⟨S, hRS, hSfg, fun R' hSR' hR E0 q' r hr hf' => ?_⟩
  refine hS R' hSR' hR E0 _ (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R'))) p)
    (pullback.lift q' (r ≫ f) hf'.symm) r (cmp p (incl hR) _ _ (incl_sk hR)) (paste p _ _ _ (incl_sk hR))
    (by rw [pullback.lift_fst, pullback.lift_fst]; exact hr) ?_
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]; exact hr.w.symm
  · simp only [Category.assoc, pullback.lift_snd]

end LateralTheory.E.LocallyQuasiFiniteGraphSpreadingOut

end

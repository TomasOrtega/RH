import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

noncomputable section
namespace GlobalTheory.CechOne

/- English proof (translation)
Establish `H` using `isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A B B)`. Establish `e0 : y1 A B 0 = Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)` using `rfl`. Establish `e1 : y1 A B 1 = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom)` using `rfl`. Use `⟨WidePullbackCone.IsLimit.mk _ (fun t => H.lift (t.π 0) (t.π 1) ?_) ?_ ?_ ?_⟩` and prove the remaining obligations. Conclude with `(t.condition 0).trans (t.condition 1).symm`.

Introduce `t`. Express the relevant statement in the definitionally equal form `_ ≫ Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B))) = _`. Rewrite using `[← hy1 A B 0, ← Category.assoc, e0, H.lift_fst]`. Conclude with `t.condition 0`. Introduce `t i fin_cases i`.

Conclude with `H.lift_fst _ _ _`. Conclude with `H.lift_snd _ _ _`. Introduce `t m _ hm`. Apply `H.hom_ext` to reduce the goal to its premises. Rewrite using `[H.lift_fst, ← hm 0]`.

Both sides reduce to the same expression. Rewrite using `[H.lift_snd, ← hm 1]`. Both sides reduce to the same expression.
-/
theorem isLimit_widePullback_tensor (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin (1 + 1) => GlobalTheory.CechOne.fB A B)
      (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B)))) (GlobalTheory.CechOne.y1 A B) (GlobalTheory.CechOne.hy1 A B))) := by
  have H := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A B B)
  have e0 : y1 A B 0 = Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := rfl
  have e1 : y1 A B 1 = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom) := rfl
  refine ⟨WidePullbackCone.IsLimit.mk _ (fun t => H.lift (t.π 0) (t.π 1) ?_) ?_ ?_ ?_⟩
  · exact (t.condition 0).trans (t.condition 1).symm
  · intro t
    change _ ≫ Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B))) = _
    rw [← hy1 A B 0, ← Category.assoc, e0, H.lift_fst]
    exact t.condition 0
  · intro t i
    fin_cases i
    · exact H.lift_fst _ _ _
    · exact H.lift_snd _ _ _
  · intro t m _ hm
    apply H.hom_ext
    · rw [H.lift_fst, ← hm 0]; rfl
    · rw [H.lift_snd, ← hm 1]; rfl

end GlobalTheory.CechOne

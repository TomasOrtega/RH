import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyHomExtPoints
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

/- English proof (translation)
Take `⟨⟨z, φ⟩, rfl⟩` from `(Scheme.SpecToEquivOfField L X).symm.surjective y`. Take `⟨⟨z', α⟩, rfl⟩` from `(Scheme.SpecToEquivOfField K X).symm.surjective e`. Simplify using `only [Scheme.SpecToEquivOfField_symm_apply] at he hy h ⊢`. Establish `hz : z = z'` using `by simpa using h`. Substitute `hz` using the available equality.

Take `⟨c, hc⟩` from `Spec.map_surjective (X.fromSpecResidueField z ≫ t)`. Rewrite `he` using `[Category.assoc, ← hc, ← Spec.map_comp, ← Spec.map_id]`. Rewrite `hy` using `[Category.assoc, ← hc, ← Spec.map_comp]`. Establish `h₁` using `Spec.map_injective he`. Establish `e₁ : ∀ k, α.hom (c.hom k) = k` using `fun k => congrArg (fun r => r.hom k) h₁`.

Substitute `hy` using the available equality. Rewrite using `[← Category.assoc, ← Spec.map_comp]`. Use `congr 1`. Use `congr 1`. Use extensionality with `w`.

Establish `e₂ : c.hom (α.hom w) = w` using `α.hom.injective (e₁ _)`. Simplify using `[e₂]`.
-/
theorem eq_comp_section_of_apply_eq {K L : Type} [Field K] [Field L] {X : Scheme.{0}} (t : X ⟶ Sp K)
    (e : Sp K ⟶ X) (he : e ≫ t = 𝟙 _) (q : Sp L ⟶ Sp K) (y : Sp L ⟶ X) (hy : y ≫ t = q)
    (p : Sp L) (p' : Sp K) (h : y p = e p') : y = q ≫ e := by
  obtain ⟨⟨z, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField L X).symm.surjective y
  obtain ⟨⟨z', α⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective e
  simp only [Scheme.SpecToEquivOfField_symm_apply] at he hy h ⊢
  have hz : z = z' := by simpa using h
  subst hz
  obtain ⟨c, hc⟩ := Spec.map_surjective (X.fromSpecResidueField z ≫ t)
  rw [Category.assoc, ← hc, ← Spec.map_comp, ← Spec.map_id] at he
  rw [Category.assoc, ← hc, ← Spec.map_comp] at hy
  have h₁ := Spec.map_injective he
  have e₁ : ∀ k, α.hom (c.hom k) = k := fun k => congrArg (fun r => r.hom k) h₁
  subst hy
  rw [← Category.assoc, ← Spec.map_comp]
  congr 1
  congr 1
  ext w
  have e₂ : c.hom (α.hom w) = w := α.hom.injective (e₁ _)
  simp [e₂]

/- English proof (translation)
Introduce `K _ A B f hf`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hf` to reduce the goal to its premises. Use `ext_of_pt_eq K A B f 0 fun x => ?_` and prove the remaining obligations.

Rewrite using `[zero_hom]`. Set `e : Sp K ⟶ B.X.left` to `(1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left`. Establish `he : e ≫ B.X.hom = 𝟙 _` using `Over.w (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X)`. Establish `h1 : (x ≫ (1 : A.X ⟶ B.X)).left = (ptOver K (AlgebraicClosure K)).hom ≫ e`. Establish `hP : (toUnit (ptOver K (AlgebraicClosure K))).left = (ptOver K (AlgebraicClosure K)).hom`.

Simplify using `using Over.w (toUnit (ptOver K (AlgebraicClosure K)))`. Establish `hU : toUnit (Over.mk (𝟙 (Sp K))) = 𝟙 _` using `toUnit_unique _ _`. Simplify using `only [e, Hom.one_def, ← Category.assoc, comp_toUnit, hU, Category.id_comp, Over.comp_left, hP]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[h1]`.

Conclude with `eq_comp_section_of_apply_eq B.X.hom e he _ _ (Over.w (x ≫ f.hom)) (IsLocalRing.closedPoint _) (IsLocalRing.closedPoint K) (hcon _)`.
-/
theorem exists_apply_ne_origin : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), f ≠ 0 →
    ∃ a : A.X.left, f.hom.left a ≠ B.origin := by
  intro K _ A B f hf
  by_contra hcon
  push_neg at hcon
  apply hf
  refine ext_of_pt_eq K A B f 0 fun x => ?_
  rw [zero_hom]
  let e : Sp K ⟶ B.X.left := (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left
  have he : e ≫ B.X.hom = 𝟙 _ := Over.w (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X)
  have h1 : (x ≫ (1 : A.X ⟶ B.X)).left = (ptOver K (AlgebraicClosure K)).hom ≫ e := by
    have hP : (toUnit (ptOver K (AlgebraicClosure K))).left = (ptOver K (AlgebraicClosure K)).hom := by
      simpa using Over.w (toUnit (ptOver K (AlgebraicClosure K)))
    have hU : toUnit (Over.mk (𝟙 (Sp K))) = 𝟙 _ := toUnit_unique _ _
    simp only [e, Hom.one_def, ← Category.assoc, comp_toUnit, hU, Category.id_comp, Over.comp_left, hP]
  apply Over.OverMorphism.ext
  rw [h1]
  exact eq_comp_section_of_apply_eq B.X.hom e he _ _ (Over.w (x ≫ f.hom))
    (IsLocalRing.closedPoint _) (IsLocalRing.closedPoint K) (hcon _)

end GlobalTheory.AV.AbVar

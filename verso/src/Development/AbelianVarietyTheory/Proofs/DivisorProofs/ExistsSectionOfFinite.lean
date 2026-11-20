import Mathlib

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.FiniteSectionLift

/- English proof (translation)
Establish `hmem : ∀ a, f.hom a ∈ φ.hom.range`. Introduce `a`. Take `⟨q, hq, h0⟩` from `hg.to_isIntegral a`. Take `⟨r, hr⟩` from `hint (f.hom a) ⟨q, hq, by`. Rewrite using `[← hf, CommRingCat.hom_comp, ← Polynomial.hom_eval₂, h0, map_zero]⟩`.

Conclude with `⟨r, hr⟩`. Set `e : R ≃+* φ.hom.range` to `RingEquiv.ofBijective φ.hom.rangeRestrict ⟨fun a b h => hinj (congrArg Subtype.val h), φ.hom.rangeRestrict_surjective⟩`. Set `t : A →+* R` to `e.symm.toRingHom.comp (f.hom.codRestrict φ.hom.range hmem)`. Establish `hkey : ∀ a, φ.hom (t a) = f.hom a`. Introduce `a`.

Establish `h1 : e (e.symm ⟨f.hom a, hmem a⟩) = ⟨f.hom a, hmem a⟩` using `e.apply_symm_apply _`. Conclude with `congrArg Subtype.val h1`. Use `⟨CommRingCat.ofHom t, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `r`. Apply `hinj` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `φ.hom (t (g.hom r)) = φ.hom r`. Rewrite using `[hkey, ← hf]`. Both sides reduce to the same expression. Use extensionality with `a`. Conclude with `hkey a`.
-/
theorem exists_section_of_finite (R A K : CommRingCat) (φ : R ⟶ K)
    (hinj : Function.Injective φ.hom)
    (hint : ∀ x : K, φ.hom.IsIntegralElem x → ∃ r : R, φ.hom r = x)
    (g : R ⟶ A) (hg : g.hom.Finite) (f : A ⟶ K) (hf : g ≫ f = φ) :
    ∃ s : A ⟶ R, g ≫ s = 𝟙 R ∧ s ≫ φ = f := by
  have hmem : ∀ a, f.hom a ∈ φ.hom.range := by
    intro a
    obtain ⟨q, hq, h0⟩ := hg.to_isIntegral a
    obtain ⟨r, hr⟩ := hint (f.hom a) ⟨q, hq, by
      rw [← hf, CommRingCat.hom_comp, ← Polynomial.hom_eval₂, h0, map_zero]⟩
    exact ⟨r, hr⟩
  let e : R ≃+* φ.hom.range := RingEquiv.ofBijective φ.hom.rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), φ.hom.rangeRestrict_surjective⟩
  let t : A →+* R := e.symm.toRingHom.comp (f.hom.codRestrict φ.hom.range hmem)
  have hkey : ∀ a, φ.hom (t a) = f.hom a := by
    intro a
    have h1 : e (e.symm ⟨f.hom a, hmem a⟩) = ⟨f.hom a, hmem a⟩ := e.apply_symm_apply _
    exact congrArg Subtype.val h1
  refine ⟨CommRingCat.ofHom t, ?_, ?_⟩
  · ext r
    apply hinj
    change φ.hom (t (g.hom r)) = φ.hom r
    rw [hkey, ← hf]
    rfl
  · ext a
    exact hkey a

/- English proof (translation)
Introduce `R K φ hinj hint Z P p ξ₀ y hp hy`. Use `haveI : IsAffine (pullback p ξ₀) := isAffine_of_isAffineHom (pullback.snd p ξ₀)`. Set `l : Spec K ⟶ pullback p ξ₀` to `pullback.lift y (Spec.map φ) hy`. Set `g : R ⟶ Γ(pullback p ξ₀, ⊤)` to `Spec.preimage ((pullback p ξ₀).isoSpec.inv ≫ pullback.snd p ξ₀)`. Set `f : Γ(pullback p ξ₀, ⊤) ⟶ K` to `Spec.preimage (l ≫ (pullback p ξ₀).isoSpec.hom)`.

Establish `hgS : Spec.map g = (pullback p ξ₀).isoSpec.inv ≫ pullback.snd p ξ₀` using `Spec.map_preimage _`. Establish `hfS : Spec.map f = l ≫ (pullback p ξ₀).isoSpec.hom` using `Spec.map_preimage _`. Establish `hgfin : g.hom.Finite`. Rewrite using `[← IsFinite.SpecMap_iff, hgS]`. Use `infer_instance`.

Establish `hf : g ≫ f = φ`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hfS, hgS]`. Simplify using `only [l, Category.assoc, Iso.hom_inv_id_assoc]`. Conclude with `pullback.lift_snd _ _ _`.

Take `⟨s, hs1, hs2⟩` from `exists_section_of_finite R _ K φ hinj hint g hgfin f hf`. Use `⟨Spec.map s ≫ (pullback p ξ₀).isoSpec.inv ≫ pullback.fst p ξ₀, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, ← Spec.map_comp, hs2, hfS]`. Simplify using `only [l, Category.assoc, Iso.hom_inv_id_assoc]`. Conclude with `pullback.lift_fst _ _ _`.

Rewrite using `[Category.assoc, Category.assoc, pullback.condition, ← Category.assoc _ (pullback.snd p ξ₀), ← hgS, ← Category.assoc, ← Spec.map_comp, hs1, Spec.map_id, Category.id_comp]`.
-/
theorem lift_of_finite : ∀ (R K : CommRingCat) (φ : R ⟶ K),
    Function.Injective (⇑(CommRingCat.Hom.hom φ) : (↑R : Type) → (↑K : Type)) →
    (∀ (x : (↑K : Type)), RingHom.IsIntegralElem (CommRingCat.Hom.hom φ) x →
      ∃ (r : (↑R : Type)), (CommRingCat.Hom.hom φ : (↑R : Type) → (↑K : Type)) r = x) →
    ∀ (Z P : AlgebraicGeometry.Scheme) (p : Z ⟶ P) (ξ₀ : AlgebraicGeometry.Spec R ⟶ P)
      (y : AlgebraicGeometry.Spec K ⟶ Z), AlgebraicGeometry.IsFinite p →
      CategoryTheory.CategoryStruct.comp y p =
        CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Spec.map φ) ξ₀ →
      ∃ (ξ : AlgebraicGeometry.Spec R ⟶ Z),
        CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Spec.map φ) ξ = y ∧
        CategoryTheory.CategoryStruct.comp ξ p = ξ₀ := by
  intro R K φ hinj hint Z P p ξ₀ y hp hy
  haveI : IsAffine (pullback p ξ₀) := isAffine_of_isAffineHom (pullback.snd p ξ₀)
  let l : Spec K ⟶ pullback p ξ₀ := pullback.lift y (Spec.map φ) hy
  let g : R ⟶ Γ(pullback p ξ₀, ⊤) :=
    Spec.preimage ((pullback p ξ₀).isoSpec.inv ≫ pullback.snd p ξ₀)
  let f : Γ(pullback p ξ₀, ⊤) ⟶ K := Spec.preimage (l ≫ (pullback p ξ₀).isoSpec.hom)
  have hgS : Spec.map g = (pullback p ξ₀).isoSpec.inv ≫ pullback.snd p ξ₀ := Spec.map_preimage _
  have hfS : Spec.map f = l ≫ (pullback p ξ₀).isoSpec.hom := Spec.map_preimage _
  have hgfin : g.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hgS]
    infer_instance
  have hf : g ≫ f = φ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hfS, hgS]
    simp only [l, Category.assoc, Iso.hom_inv_id_assoc]
    exact pullback.lift_snd _ _ _
  obtain ⟨s, hs1, hs2⟩ := exists_section_of_finite R _ K φ hinj hint g hgfin f hf
  refine ⟨Spec.map s ≫ (pullback p ξ₀).isoSpec.inv ≫ pullback.fst p ξ₀, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, hs2, hfS]
    simp only [l, Category.assoc, Iso.hom_inv_id_assoc]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc _ (pullback.snd p ξ₀),
      ← hgS, ← Category.assoc, ← Spec.map_comp, hs1, Spec.map_id, Category.id_comp]

end GlobalTheory.FiniteSectionLift

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.PullbackFinitePoint

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in

/- English proof (translation)
Use `letI := (f.residueFieldMap x).hom.toAlgebra`. Unfold `Scheme.Hom.residueDegree RingHom.Finite`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h)`.

Introduce `h`. Conclude with `Module.finrank_pos.ne'`.
-/
theorem _root_.GlobalTheory.PullbackFinitePoint.residueDegree_ne_zero_iff_finite {X Y : Scheme.{0}} (f : X ⟶ Y) (x : X) :
    f.residueDegree x ≠ 0 ↔ (f.residueFieldMap x).hom.Finite := by
  letI := (f.residueFieldMap x).hom.toAlgebra
  unfold Scheme.Hom.residueDegree RingHom.Finite
  constructor
  · intro h
    exact Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h)
  · intro h
    exact Module.finrank_pos.ne'

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
/- English proof (translation)
Introduce `z`. Take `⟨s, rfl⟩` from `X.residue_surjective x z`. Take `⟨t, rfl⟩` from `f.stalkMap_surjective x s`. Use `⟨Y.residue (f x) t, ?_⟩` and prove the remaining obligations. Rewrite using `[← ConcreteCategory.comp_apply, Scheme.residue_residueFieldMap, ConcreteCategory.comp_apply]`.
-/
private theorem residueFieldMap_surjective_of_surjectiveOnStalks {X Y : Scheme.{0}} (f : X ⟶ Y)
    [SurjectiveOnStalks f] (x : X) : Function.Surjective (f.residueFieldMap x) := by
  intro z
  obtain ⟨s, rfl⟩ := X.residue_surjective x z
  obtain ⟨t, rfl⟩ := f.stalkMap_surjective x s
  refine ⟨Y.residue (f x) t, ?_⟩
  rw [← ConcreteCategory.comp_apply, Scheme.residue_residueFieldMap, ConcreteCategory.comp_apply]

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in

/- English proof (translation)
The claim follows from `(_root_.GlobalTheory.PullbackFinitePoint.residueDegree_ne_zero_iff_finite f x).2 (RingHom.Finite.of_surjective _ (residueFieldMap_surjective_of_surjectiveOnStalks f x))`.
-/
theorem _root_.GlobalTheory.PullbackFinitePoint.residueDegree_ne_zero_of_surjectiveOnStalks {X Y : Scheme.{0}} (f : X ⟶ Y)
    [SurjectiveOnStalks f] (x : X) : f.residueDegree x ≠ 0 :=
  (_root_.GlobalTheory.PullbackFinitePoint.residueDegree_ne_zero_iff_finite f x).2
    (RingHom.Finite.of_surjective _ (residueFieldMap_surjective_of_surjectiveOnStalks f x))

/- English proof (translation)
Rewrite using `[residueDegree_ne_zero_iff_finite]`. Establish `hb : Function.Surjective ((Scheme.ΓSpecIso (.of L)).inv ≫ (Spec (.of L)).Γevaluation q).hom`. Establish `: Subsingleton (Spec (CommRingCat.of L))` using `inferInstanceAs (Subsingleton (PrimeSpectrum L))`. Introduce `a`. Take `⟨b, rfl⟩` from `(Spec (.of L)).residue_surjective _ a`.

Take `⟨U, hU, c, rfl⟩` from `(Spec (.of L)).presheaf.exists_germ_eq b`. Take `rfl : U = ⊤` from `top_le_iff.1 fun y _ => Subsingleton.elim q y ▸ hU`. Take `⟨r, rfl⟩` from `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of L)).inv).2 c`. Conclude with `⟨r, rfl⟩`. Establish `e : ((Scheme.ΓSpecIso K).inv ≫ (Spec K).Γevaluation (Spec.map φ q)) ≫ (Spec.map φ).residueFieldMap q = φ ≫ (Scheme.ΓSpecIso (.of L)).inv ≫ (Spec (.of L)).Γevaluation q`.

Rewrite using `[Category.assoc, Scheme.Γevaluation_naturality, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]`. Establish `h` using `(RingHom.Finite.of_surjective _ hb).comp hφ`. Rewrite `h` using `[← CommRingCat.hom_comp, ← e, CommRingCat.hom_comp]`. Conclude with `h.of_comp_finite`.
-/
theorem residueDegree_SpecMap_ne_zero {K : CommRingCat.{0}} {L : Type} [Field L]
    (φ : K ⟶ CommRingCat.of L) (hφ : φ.hom.Finite) (q : Spec (CommRingCat.of L)) :
    (Spec.map φ).residueDegree q ≠ 0 := by
  rw [residueDegree_ne_zero_iff_finite]
  have hb : Function.Surjective
      ((Scheme.ΓSpecIso (.of L)).inv ≫ (Spec (.of L)).Γevaluation q).hom := by
    have : Subsingleton (Spec (CommRingCat.of L)) := inferInstanceAs (Subsingleton (PrimeSpectrum L))
    intro a
    obtain ⟨b, rfl⟩ := (Spec (.of L)).residue_surjective _ a
    obtain ⟨U, hU, c, rfl⟩ := (Spec (.of L)).presheaf.exists_germ_eq b
    obtain rfl : U = ⊤ := top_le_iff.1 fun y _ => Subsingleton.elim q y ▸ hU
    obtain ⟨r, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of L)).inv).2 c
    exact ⟨r, rfl⟩
  have e : ((Scheme.ΓSpecIso K).inv ≫ (Spec K).Γevaluation (Spec.map φ q)) ≫
      (Spec.map φ).residueFieldMap q =
      φ ≫ (Scheme.ΓSpecIso (.of L)).inv ≫ (Spec (.of L)).Γevaluation q := by
    rw [Category.assoc, Scheme.Γevaluation_naturality, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  have h := (RingHom.Finite.of_surjective _ hb).comp hφ
  rw [← CommRingCat.hom_comp, ← e, CommRingCat.hom_comp] at h
  exact h.of_comp_finite

/- English proof (translation)
Establish `h₁` using `CurveDegreesCompare.residueDegree_comp w π q`. Rewrite `h₁` using `[h, CurveDegreesCompare.residueDegree_comp]`. Establish `h₂` using `mul_ne_zero (residueDegree_ne_zero_of_surjectiveOnStalks (Y.fromSpecResidueField y) (Spec.map φ q)) (residueDegree_SpecMap_ne_zero φ hφ q)`. Rewrite `h₂` using `[h₁]`. Conclude with `left_ne_zero_of_mul h₂`.
-/
theorem residueDegree_ne_zero_of_fieldPoint {P Y : Scheme.{0}} {L : Type} [Field L]
    (w : Spec (CommRingCat.of L) ⟶ P) (π : P ⟶ Y) (y : Y)
    (φ : Y.residueField y ⟶ CommRingCat.of L) (hφ : φ.hom.Finite)
    (h : w ≫ π = Spec.map φ ≫ Y.fromSpecResidueField y) (q : Spec (CommRingCat.of L)) :
    π.residueDegree (w q) ≠ 0 := by
  have h₁ := CurveDegreesCompare.residueDegree_comp w π q
  rw [h, CurveDegreesCompare.residueDegree_comp] at h₁
  have h₂ := mul_ne_zero (residueDegree_ne_zero_of_surjectiveOnStalks
    (Y.fromSpecResidueField y) (Spec.map φ q)) (residueDegree_SpecMap_ne_zero φ hφ q)
  rw [h₁] at h₂
  exact left_ne_zero_of_mul h₂

/- English proof (translation)
Introduce `X Y₁ Y₂ f g y₁ y₂ h h₁ h₂`. Set `T : Scheme.Pullback.Triplet f g` to `Scheme.Pullback.Triplet.mk' y₁ y₂ h`. Establish `hf : ((X.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom.Finite` using `((residueDegree_ne_zero_iff_finite f y₁).1 h₁).comp (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (X.residueFieldCongr T.hx).inv).2)`. Establish `hg : ((X.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom.Finite` using `((residueDegree_ne_zero_iff_finite g y₂).1 h₂).comp (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (X.residueFieldCongr T.hy).inv).2)`. Establish `hl : T.tensorInl.hom.Finite` using `RingHom.finite_isStableUnderBaseChange.pushout_inl RingHom.finite_respectsIso _ _ hg`.

Establish `hr : T.tensorInr.hom.Finite`. Establish `h₃` using `RingHom.finite_isStableUnderBaseChange.pushout_inl RingHom.finite_respectsIso ((X.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y) _ hf`. Apply the tactic sequence `have h₄ := (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (Limits.pushoutSymmetry ((X.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y) ((X.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)).hom).2).comp h₃`. Establish `e` using `Limits.inl_comp_pushoutSymmetry_hom ((X.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y) ((X.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)`. Conclude with `congr($(e).hom.Finite) ▸ h₄`.

Take `⟨m, hm⟩` from `Ideal.exists_maximal T.tensor`. Use `letI := Ideal.Quotient.field m`. Set `ρ : T.tensor ⟶ CommRingCat.of (T.tensor ⧸ m)` to `CommRingCat.ofHom (Ideal.Quotient.mk m)`. Establish `hρ : ρ.hom.Finite` using `RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective`. Set `q : Spec (CommRingCat.of (T.tensor ⧸ m))` to `(⊥ : PrimeSpectrum (T.tensor ⧸ m))`.

Use `⟨(Spec.map ρ ≫ T.SpecTensorTo) q, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `T.fst_SpecTensorTo_apply _`. Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `T.snd_SpecTensorTo_apply _`.

Use `residueDegree_ne_zero_of_fieldPoint _ _ T.x (T.tensorInl ≫ ρ) (hρ.comp hl) ?_ q` and prove the remaining obligations. Rewrite using `[Category.assoc, T.specTensorTo_fst, Spec.map_comp, Category.assoc]`. Use `residueDegree_ne_zero_of_fieldPoint _ _ T.y (T.tensorInr ≫ ρ) (hρ.comp hr) ?_ q` and prove the remaining obligations. Rewrite using `[Category.assoc, T.specTensorTo_snd, Spec.map_comp, Category.assoc]`.
-/
theorem exists_point : ∀ (X Y₁ Y₂ : Scheme.{0}) (f : Y₁ ⟶ X) (g : Y₂ ⟶ X) (y₁ : Y₁) (y₂ : Y₂),
    f y₁ = g y₂ → f.residueDegree y₁ ≠ 0 → g.residueDegree y₂ ≠ 0 →
    ∃ z : ↥(Limits.pullback f g), (Limits.pullback.fst f g) z = y₁ ∧
      (Limits.pullback.snd f g) z = y₂ ∧ (Limits.pullback.fst f g).residueDegree z ≠ 0 ∧
      (Limits.pullback.snd f g).residueDegree z ≠ 0 := by
  intro X Y₁ Y₂ f g y₁ y₂ h h₁ h₂
  let T : Scheme.Pullback.Triplet f g := Scheme.Pullback.Triplet.mk' y₁ y₂ h
  have hf : ((X.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom.Finite :=
    ((residueDegree_ne_zero_iff_finite f y₁).1 h₁).comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (X.residueFieldCongr T.hx).inv).2)
  have hg : ((X.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom.Finite :=
    ((residueDegree_ne_zero_iff_finite g y₂).1 h₂).comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (X.residueFieldCongr T.hy).inv).2)
  have hl : T.tensorInl.hom.Finite :=
    RingHom.finite_isStableUnderBaseChange.pushout_inl RingHom.finite_respectsIso _ _ hg
  have hr : T.tensorInr.hom.Finite := by
    have h₃ := RingHom.finite_isStableUnderBaseChange.pushout_inl RingHom.finite_respectsIso
      ((X.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y) _ hf
    have h₄ := (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso
      (Limits.pushoutSymmetry ((X.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)
        ((X.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)).hom).2).comp h₃
    have e := Limits.inl_comp_pushoutSymmetry_hom
      ((X.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)
      ((X.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
    exact congr($(e).hom.Finite) ▸ h₄
  obtain ⟨m, hm⟩ := Ideal.exists_maximal T.tensor
  letI := Ideal.Quotient.field m
  let ρ : T.tensor ⟶ CommRingCat.of (T.tensor ⧸ m) := CommRingCat.ofHom (Ideal.Quotient.mk m)
  have hρ : ρ.hom.Finite := RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective
  let q : Spec (CommRingCat.of (T.tensor ⧸ m)) := (⊥ : PrimeSpectrum (T.tensor ⧸ m))
  refine ⟨(Spec.map ρ ≫ T.SpecTensorTo) q, ?_, ?_, ?_, ?_⟩
  · rw [Scheme.Hom.comp_apply]
    exact T.fst_SpecTensorTo_apply _
  · rw [Scheme.Hom.comp_apply]
    exact T.snd_SpecTensorTo_apply _
  · refine residueDegree_ne_zero_of_fieldPoint _ _ T.x (T.tensorInl ≫ ρ) (hρ.comp hl) ?_ q
    rw [Category.assoc, T.specTensorTo_fst, Spec.map_comp, Category.assoc]
  · refine residueDegree_ne_zero_of_fieldPoint _ _ T.y (T.tensorInr ≫ ρ) (hρ.comp hr) ?_ q
    rw [Category.assoc, T.specTensorTo_snd, Spec.map_comp, Category.assoc]

end GlobalTheory.PullbackFinitePoint

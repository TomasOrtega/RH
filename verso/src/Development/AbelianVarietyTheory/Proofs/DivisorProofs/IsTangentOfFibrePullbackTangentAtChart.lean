import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChartPtChartPt
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Introduce `E _ _ _ H X t U n v hv K _ x0 hU A _ m u hm hu a`. Establish `hunit : η[A].left ≫ m = x0 ≫ η[t.G].left`. Establish `hw : (η[A].left ≫ m) ≫ t.G.hom = (𝟙_ (Over (Sp K))).hom ≫ x0`. Rewrite using `[Category.assoc, hm.1.w, ← Category.assoc, Over.w η[A]]`. Set `p : Over.mk ((𝟙_ (Over (Sp K))).hom ≫ x0) ⟶ t.G` to `Over.homMk (η[A].left ≫ m) hw`.

Establish `h1 : (1 : 𝟙_ (Over (Sp K)) ⟶ A) = η[A]`. Rewrite using `[Hom.one_def, toUnit_unit, Category.id_comp]`. Establish `hpp` using `hm.2 (𝟙_ (Over (Sp K))) 1 1 p p (by rw [h1]; rfl) (by rw [h1]; rfl)`. Rewrite `hpp` using `[_root_.mul_one, h1]`. Establish `hp : p * p = p` using `Over.OverMorphism.ext hpp`.

Establish `hp1 : p = 1` using `mul_eq_left.mp hp`. Use `congrArg (fun q => q.left) hp1` as an intermediate fact. Simplify using `only [p, Over.homMk_left, Hom.one_def, Over.comp_left, Over.toUnit_left, Over.mk_hom] at this`. Rewrite using `[this]`. Simplify using the standard rewrite rules.

Use `show spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ (u a).left = η[A].left`. Apply `hm.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hu a, hunit, ← Category.assoc, ← Spec.map_comp]`. Establish `hr : CommRingCat.ofHom (dualMap (ev x0 U.1 hU)) ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom = CommRingCat.ofHom (TrivSqZeroExt.fstHom Γ(X, U.1) Γ(X, U.1) Γ(X, U.1)).toRingHom ≫ CommRingCat.ofHom (ev x0 U.1 hU)`. Apply `CommRingCat.hom_ext` to reduce the goal to its premises.

Apply `RingHom.ext` to reduce the goal to its premises. Introduce `x`. Simplify using `[dualMap]`. Rewrite using `[hr, Spec.map_comp, Category.assoc, (hv a).2, Hom.one_def, Over.comp_left, Over.toUnit_left, ← Category.assoc]`. Use `congr 1`.

Conclude with `GlobalTheory.FlagMod.spMap_ev x0 U.2 hU`. Rewrite using `[Category.assoc, Over.w (u a), Over.w η[A]] show Spec.map _ ≫ Spec.map _ = _`. Rewrite using `[← Spec.map_comp]`. Use `show _ = 𝟙 (Sp K)`. Rewrite using `[← Spec.map_id]`.

Use `congr 1`.
-/
theorem GlobalTheory.CechKS.isTangent_of_fibre : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) (U : X.affineOpens) {n : ℕ} (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (hv : ∀ a, IsTanAtG t (LogKS.chart U) (v a)) {K : Type} [Field K] (x0 : Sp K ⟶ X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1) (A : Over (Sp K)) [GrpObj A] (m : A.left ⟶ t.G.left) (u : Fin n → (epsR K ⟶ A)) (hm : IsGrpPullback A t.G x0 m) (hu : ∀ a, (u a).left ≫ m = spMap (dualMap (ev x0 U.1 hU)) ≫ v a) (a : Fin n), IsTangent (u a) := by
  intro E _ _ _ H X t U n v hv K _ x0 hU A _ m u hm hu a

  have hunit : η[A].left ≫ m = x0 ≫ η[t.G].left := by
    have hw : (η[A].left ≫ m) ≫ t.G.hom = (𝟙_ (Over (Sp K))).hom ≫ x0 := by
      rw [Category.assoc, hm.1.w, ← Category.assoc, Over.w η[A]]
    let p : Over.mk ((𝟙_ (Over (Sp K))).hom ≫ x0) ⟶ t.G := Over.homMk (η[A].left ≫ m) hw
    have h1 : (1 : 𝟙_ (Over (Sp K)) ⟶ A) = η[A] := by
      rw [Hom.one_def, toUnit_unit, Category.id_comp]
    have hpp := hm.2 (𝟙_ (Over (Sp K))) 1 1 p p (by rw [h1]; rfl) (by rw [h1]; rfl)
    rw [_root_.mul_one, h1] at hpp
    have hp : p * p = p := Over.OverMorphism.ext hpp
    have hp1 : p = 1 := mul_eq_left.mp hp
    have := congrArg (fun q => q.left) hp1
    simp only [p, Over.homMk_left, Hom.one_def, Over.comp_left, Over.toUnit_left, Over.mk_hom] at this
    rw [this]
    simp
  show spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ (u a).left = η[A].left
  apply hm.1.hom_ext
  · rw [Category.assoc, hu a, hunit, ← Category.assoc, ← Spec.map_comp]
    have hr : CommRingCat.ofHom (dualMap (ev x0 U.1 hU)) ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom =
        CommRingCat.ofHom (TrivSqZeroExt.fstHom Γ(X, U.1) Γ(X, U.1) Γ(X, U.1)).toRingHom ≫ CommRingCat.ofHom (ev x0 U.1 hU) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      simp [dualMap]
    rw [hr, Spec.map_comp, Category.assoc, (hv a).2, Hom.one_def, Over.comp_left, Over.toUnit_left,
      ← Category.assoc]
    congr 1
    exact GlobalTheory.FlagMod.spMap_ev x0 U.2 hU
  · rw [Category.assoc, Over.w (u a), Over.w η[A]]
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    show _ = 𝟙 (Sp K)
    rw [← Spec.map_id]
    congr 1

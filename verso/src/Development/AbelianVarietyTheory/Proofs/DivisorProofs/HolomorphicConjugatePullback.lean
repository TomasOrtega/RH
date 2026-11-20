import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionBySetPowOfDivisibleNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIsAlgClosedStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionGeometricPointsEqPowTwoDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyAndPrimeDvdDegOfDvdNorm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFieldSmoothOfRelativeDimensionExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtOverClosureIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FibreAV

section

variable {S : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ S) (A : Over S) [GrpObj A]

/- English proof (translation)
Simplify using `only [Over.pullback_map_left]`. Conclude with `pullback.lift_fst _ _ _`.
-/
theorem pull_map_left_fst {B : Over S} (f : A ⟶ B) :
    ((Over.pullback x).map f).left ≫ pullback.fst B.hom x = pullback.fst A.hom x ≫ f.left := by
  simp only [Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[he, Over.comp_left, Over.comp_left, he, Category.assoc, pull_map_left_fst, Category.assoc]`.
-/
theorem push_comp_map {T : Over (Sp k)} {g : T.left ⟶ S} (f : A ⟶ A)
    (e : (T ⟶ (Over.pullback x).obj A) → (Over.mk g ⟶ A)) (he : ∀ z, (e z).left = z.left ≫ pullback.fst A.hom x)
    (z : T ⟶ (Over.pullback x).obj A) : e (z ≫ (Over.pullback x).map f) = e z ≫ f := by
  apply Over.OverMorphism.ext
  rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, pull_map_left_fst, Category.assoc]

end

open GlobalTheory.AV.AbVar in
/- English proof (translation)
Introduce `S A _ _ hA F _ _ act k _ _ x`. Use `letI : GrpObj ((Over.pullback x).obj A) := Functor.grpObjObj`. Establish `h : IsGrpPullback ((Over.pullback x).obj A) A x (pullback.fst A.hom x)` using `isGrpPullback_pullback A x`. Establish `hab : IsAbelianScheme ((Over.pullback x).obj A)` using `GlobalTheory.isAbelianScheme_pullback_obj x A hA`. Take `⟨g, hg⟩` from `GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme k _ hab`.

Set `B : AbVar k` to `{ X := (Over.pullback x).obj A, ab := hab, dim := g, smooth := hg }`. Take `⟨e₀, he₀⟩` from `GlobalTheory.LiePull.exists_pushEquiv h (𝟙_ (Over (Sp k))) x (by simp)`. Set `e : (Over.mk x ⟶ A) ≃* B.Pt` to `e₀.symm.trans (GlobalTheory.PushEigen.ptClosureEquiv B).symm`. Establish `hm : ∀ c, IsMonHom ((Over.pullback x).map (act.act c))` using `fun c => by`. Use `act.hom c` as an intermediate fact.

Use `infer_instance`. Set `ψf : 𝓞 F → End B` to `fun c => @Hom.mk k _ B B ((Over.pullback x).map (act.act c)) (hm c)`. Establish `hψ : ∀ c, Hom.hom (ψf c) = (Over.pullback x).map (act.act c)` using `fun c => rfl`. Establish `act0 : act.act 0 = 1`. Use `act.add 0 0` as an intermediate fact.

Rewrite `this` using `[add_zero]`. Conclude with `(mul_eq_left.mp this.symm)`. Set `ψ : 𝓞 F →+* End B` to `{ toFun := ψf map_one' := by`. Apply `GlobalTheory.AV.AbVar.hom_ext` to reduce the goal to its premises. Rewrite using `[hψ, act.one, CategoryTheory.Functor.map_id]`.

Both sides reduce to the same expression. Use the proof step `map_mul' := fun a b => by`. Apply `GlobalTheory.AV.AbVar.hom_ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `_ = Hom.hom (ψf b) ≫ Hom.hom (ψf a)`. Rewrite using `[hψ, hψ, hψ, mul_comm, act.mul, CategoryTheory.Functor.map_comp]`.

Use the proof step `map_zero' := by`. Apply `GlobalTheory.AV.AbVar.hom_ext` to reduce the goal to its premises. Rewrite using `[hψ, act0, zero_hom]`. Conclude with `CategoryTheory.Functor.map_one _`. Use the proof step `map_add' := fun a b => by`.

Apply `GlobalTheory.AV.AbVar.hom_ext` to reduce the goal to its premises. Rewrite using `[add_hom, hψ, hψ, hψ, act.add]`. Conclude with `CategoryTheory.Functor.map_mul _ _ _ }`. Use `⟨B, e, ψ, fun c z => ?_, fun c H w hw1 hw2 => ?_⟩` and prove the remaining obligations. Use `show (GlobalTheory.PushEigen.ptClosureEquiv B).symm (e₀.symm (z ≫ act.act c)) = (GlobalTheory.PushEigen.ptClosureEquiv B).symm (e₀.symm z) ≫ (Over.pullback x).map (act.act c)`.

Establish `: e₀.symm (z ≫ act.act c) = e₀.symm z ≫ (Over.pullback x).map (act.act c)`. Apply `e₀.injective` to reduce the goal to its premises. Rewrite using `[MulEquiv.apply_symm_apply, push_comp_map x A (act.act c) e₀ he₀, MulEquiv.apply_symm_apply]`. Rewrite using `[this]`. Both sides reduce to the same expression.

Take `⟨e₁, he₁⟩` from `GlobalTheory.LiePull.exists_pushEquiv h (epsPtR (𝟙 (Sp k))) (spMap (algebraMap k (DualNumber k)) ≫ x) (by simp)`. Take `⟨e₂, he₂⟩` from `GlobalTheory.LiePull.exists_pushEquiv h (Over.mk (𝟙 (Sp k))) x (by simp)`. Establish `one : (1 : Over.mk x ⟶ A).left = (1 : Over.mk (𝟙 (Sp k)) ⟶ (Over.pullback x).obj A).left ≫ pullback.fst A.hom x`. Rewrite using `[← he₂, map_one]`. Establish `r1 : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (e₁ w).left = (1 : Over.mk x ⟶ A).left`.

Rewrite using `[he₁, one, ← Category.assoc, hw1]`. Establish `r2 : e₁ w ≫ act.act c = 1`. Rewrite using `[← push_comp_map x A (act.act c) e₁ he₁]`. Establish `hw2' : w ≫ Hom.hom (ψf c) = 1` using `hw2`. Express the relevant statement in the definitionally equal form `e₁ (w ≫ Hom.hom (ψf c)) = 1`.

Rewrite using `[hw2', map_one]`. Conclude with `e₁.injective ((H (e₁ w) r1 r2).trans (map_one e₁).symm)`.
-/
theorem fibre_av : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ (B : AbVar k) (e : (Over.mk x ⟶ A) ≃* B.Pt) (ψ : 𝓞 F →+* End B), (∀ (c : 𝓞 F) (g : Over.mk x ⟶ A), e (g ≫ act.act c) = e g ≫ Hom.hom (ψ c)) ∧ ∀ c : 𝓞 F, (∀ v : epsPtR x ⟶ A, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left → v ≫ act.act c = 1 → v = 1) → ∀ w : epsPtR (𝟙 (Sp k)) ⟶ B.X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ w.left = (1 : Over.mk (𝟙 (Sp k)) ⟶ B.X).left → w ≫ Hom.hom (ψ c) = 1 → w = 1 := by
  intro S A _ _ hA F _ _ act k _ _ x
  letI : GrpObj ((Over.pullback x).obj A) := Functor.grpObjObj
  have h : IsGrpPullback ((Over.pullback x).obj A) A x (pullback.fst A.hom x) := isGrpPullback_pullback A x
  have hab : IsAbelianScheme ((Over.pullback x).obj A) := GlobalTheory.isAbelianScheme_pullback_obj x A hA
  obtain ⟨g, hg⟩ := GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme k _ hab
  let B : AbVar k := { X := (Over.pullback x).obj A, ab := hab, dim := g, smooth := hg }
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv h (𝟙_ (Over (Sp k))) x (by simp)
  let e : (Over.mk x ⟶ A) ≃* B.Pt := e₀.symm.trans (GlobalTheory.PushEigen.ptClosureEquiv B).symm
  have hm : ∀ c, IsMonHom ((Over.pullback x).map (act.act c)) := fun c => by
    have := act.hom c; infer_instance
  let ψf : 𝓞 F → End B := fun c => @Hom.mk k _ B B ((Over.pullback x).map (act.act c)) (hm c)
  have hψ : ∀ c, Hom.hom (ψf c) = (Over.pullback x).map (act.act c) := fun c => rfl
  have act0 : act.act 0 = 1 := by
    have := act.add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  let ψ : 𝓞 F →+* End B :=
    { toFun := ψf
      map_one' := by
        apply GlobalTheory.AV.AbVar.hom_ext
        rw [hψ, act.one, CategoryTheory.Functor.map_id]
        rfl
      map_mul' := fun a b => by
        apply GlobalTheory.AV.AbVar.hom_ext
        change _ = Hom.hom (ψf b) ≫ Hom.hom (ψf a)
        rw [hψ, hψ, hψ, mul_comm, act.mul, CategoryTheory.Functor.map_comp]
      map_zero' := by
        apply GlobalTheory.AV.AbVar.hom_ext
        rw [hψ, act0, zero_hom]
        exact CategoryTheory.Functor.map_one _
      map_add' := fun a b => by
        apply GlobalTheory.AV.AbVar.hom_ext
        rw [add_hom, hψ, hψ, hψ, act.add]
        exact CategoryTheory.Functor.map_mul _ _ _ }
  refine ⟨B, e, ψ, fun c z => ?_, fun c H w hw1 hw2 => ?_⟩
  · show (GlobalTheory.PushEigen.ptClosureEquiv B).symm (e₀.symm (z ≫ act.act c)) =
      (GlobalTheory.PushEigen.ptClosureEquiv B).symm (e₀.symm z) ≫ (Over.pullback x).map (act.act c)
    have : e₀.symm (z ≫ act.act c) = e₀.symm z ≫ (Over.pullback x).map (act.act c) := by
      apply e₀.injective
      rw [MulEquiv.apply_symm_apply, push_comp_map x A (act.act c) e₀ he₀, MulEquiv.apply_symm_apply]
    rw [this]
    rfl
  · obtain ⟨e₁, he₁⟩ := GlobalTheory.LiePull.exists_pushEquiv h (epsPtR (𝟙 (Sp k)))
      (spMap (algebraMap k (DualNumber k)) ≫ x) (by simp)
    obtain ⟨e₂, he₂⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk (𝟙 (Sp k))) x (by simp)
    have one : (1 : Over.mk x ⟶ A).left = (1 : Over.mk (𝟙 (Sp k)) ⟶ (Over.pullback x).obj A).left ≫
        pullback.fst A.hom x := by
      rw [← he₂, map_one]
    have r1 : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (e₁ w).left = (1 : Over.mk x ⟶ A).left := by
      rw [he₁, one, ← Category.assoc, hw1]
    have r2 : e₁ w ≫ act.act c = 1 := by
      rw [← push_comp_map x A (act.act c) e₁ he₁]
      have hw2' : w ≫ Hom.hom (ψf c) = 1 := hw2
      change e₁ (w ≫ Hom.hom (ψf c)) = 1
      rw [hw2', map_one]
    exact e₁.injective ((H (e₁ w) r1 r2).trans (map_one e₁).symm)

end GlobalTheory.FibreAV

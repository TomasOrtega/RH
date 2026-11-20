import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.LeftZeroDuality.H1StructureDimLe
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteClosedSubschemeRepresentsKernelAmple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyTorsionFiniteEndomorphismDivisible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.KLFinite

/- English proof (translation)
Establish `hP : (abelian₂ A L).IsLB` using `LB.isLB_linComb hL _ _`. Establish `hl : lam (cls L hL) (fst T A ≫ x) (snd T A) = 0`. Establish `e` using `(triv_ev_iff hP _ _).1 hx`. Rewrite `e` using `[evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst, lift_snd]`. Then use the resulting hypothesis. Establish `hD : (Out.translDiff A L x).IsLB` using `LB.isLB_linComb hL _ _`.

Introduce `p`. Take `⟨V, hV, hc⟩` from `exists_pull_eq_zero (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) p`. Use `⟨V, hV, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩` and prove the remaining obligations. Establish `e₁` using `pull_translDiff hL x hD (fst T A) (snd T A)`. Rewrite `e₁` using `[lift_fst_snd, Over.id_left, pull_id]`.

Establish `e₂ : cls _ hD = CechPic.pull (fst T A).left (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL))`. Rewrite using `[e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one, ← sub_eq_zero, ← hl, lam]`. Normalize the expressions using the abelian group laws. Rewrite using `[cls_pull hD, e₂, ← pull_comp]`. Conclude with `pull_eq_zero_of_mem V (((fst T A).left ⁻¹ᵁ V).ι ≫ (fst T A).left) (fun z ↦ z.2) hc`.
-/
theorem memKL_of_triv_lam {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S}
    (x : T ⟶ A) (hx : Triv (ev (abelian₂ A L) (fst T A ≫ x) (snd T A))) : GlobalTheory.MemKL A L x := by
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have hl : lam (cls L hL) (fst T A ≫ x) (snd T A) = 0 := by
    have e := (triv_ev_iff hP _ _).1 hx
    rwa [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
      lift_snd] at e
  have hD : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
  intro p
  obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero
    (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  have e₁ := pull_translDiff hL x hD (fst T A) (snd T A)
  rw [lift_fst_snd, Over.id_left, pull_id] at e₁
  have e₂ : cls _ hD = CechPic.pull (fst T A).left
      (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) := by
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one,
      ← sub_eq_zero, ← hl, lam]
    abel
  rw [cls_pull hD, e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst T A).left ⁻¹ᵁ V).ι ≫ (fst T A).left) (fun z ↦ z.2) hc

/- English proof (translation)
Substitute `e` using the available equality. Establish `e : x = x'` using `Over.OverMorphism.ext hl`. Rewrite using `[← e]` and apply the resulting hypothesis.
-/
theorem memKL_congr {S X : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {t t' : X ⟶ S} (e : t = t')
    (x : Over.mk t ⟶ A) (x' : Over.mk t' ⟶ A) (hl : x.left = x'.left) (h : GlobalTheory.MemKL A L x) :
    GlobalTheory.MemKL A L x' := by
  subst e
  have e : x = x' := Over.OverMorphism.ext hl
  rwa [← e]

/- English proof (translation)
Take `⟨H, j, -, hfin, hH⟩` from `GlobalTheory.KernelRep.exists_finite_closed_kernel GlobalTheory.abelianSchemeLaws_all.1.globalFns k B hB M hM hA`. Establish `: IsFinite H.hom` using `hfin`. Establish `: IsFinite (toUnit H).left` using `hfin`. Establish `hf` using `GlobalTheory.TorsionDivisible.finite_fibre_points (toUnit H) (𝟙 _)`. Use `Finite.of_surjective (fun z : {x : 𝟙_ (Over (Sp k)) ⟶ H // x ≫ toUnit H = 𝟙 _} ↦ (⟨z.1 ≫ j, (hH _ _).2 ⟨z.1, rfl⟩⟩ : {x : 𝟙_ (Over (Sp k)) ⟶ B // GlobalTheory.MemKL B M x})) fun x ↦ ?_` and prove the remaining obligations.

Take `⟨z, hz⟩` from `(hH _ _).1 x.2`. Conclude with `⟨⟨z, toUnit_unique _ _⟩, Subtype.ext hz⟩`.
-/
theorem finite_memKL (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (hB : IsAbelianScheme B)
    (M : LB B.left) (hM : M.IsLB) (hA : Out.RelAmple B M) :
    Finite {x : 𝟙_ (Over (Sp k)) ⟶ B // GlobalTheory.MemKL B M x} := by
  obtain ⟨H, j, -, hfin, hH⟩ :=
    GlobalTheory.KernelRep.exists_finite_closed_kernel GlobalTheory.abelianSchemeLaws_all.1.globalFns k B hB M hM hA
  have : IsFinite H.hom := hfin
  have : IsFinite (toUnit H).left := hfin
  have hf := GlobalTheory.TorsionDivisible.finite_fibre_points (toUnit H) (𝟙 _)
  refine Finite.of_surjective
    (fun z : {x : 𝟙_ (Over (Sp k)) ⟶ H // x ≫ toUnit H = 𝟙 _} ↦
      (⟨z.1 ≫ j, (hH _ _).2 ⟨z.1, rfl⟩⟩ : {x : 𝟙_ (Over (Sp k)) ⟶ B // GlobalTheory.MemKL B M x})) fun x ↦ ?_
  obtain ⟨z, hz⟩ := (hH _ _).1 x.2
  exact ⟨⟨z, toUnit_unique _ _⟩, Subtype.ext hz⟩

/- English proof (translation)
Introduce `S A _ hA L hL hamp k _ _ t`. Set `B : Over (Sp k)` to `(Over.pullback t).obj A`. Establish `gp : IsGrpPullback B A t (pullback.fst A.hom t)` using `isGrpPullback_pullback A t`. Establish `hB : IsAbelianScheme B` using `PolPull.isAbelianScheme_of_isGrpPullback hA gp`. Use `hA.proper` as an intermediate fact.

Establish `hM : (L.pull (pullback.fst A.hom t)).IsLB` using `pull_isLB hL _`. Establish `hAmp : Out.RelAmple B (L.pull (pullback.fst A.hom t))` using `GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL hamp (IsPullback.of_hasPullback A.hom t)`. Establish `hK` using `finite_memKL k B hB _ hM hAmp`. Establish `hw : ∀ x : Over.mk t ⟶ A, x.left ≫ A.hom = 𝟙 (Sp k) ≫ t` using `fun x ↦ by`. Rewrite using `[Over.w x, Category.id_comp]`.

Both sides reduce to the same expression. Set `pt : (Over.mk t ⟶ A) → (𝟙_ (Over (Sp k)) ⟶ B)` to `fun x ↦ GlobalTheory.AbDual.liftPt gp (𝟙 _) x.left (hw x)`. Establish `hpt : ∀ x, (pt x).left ≫ pullback.fst A.hom t = x.left` using `fun x ↦ GlobalTheory.AbDual.liftPt_left gp _ _ _`. Establish `hmem : ∀ x : Over.mk t ⟶ A, Triv (ev (abelian₂ A L) (fst (Over.mk t) A ≫ x) (snd (Over.mk t) A)) → GlobalTheory.MemKL B (L.pull (pullback.fst A.hom t)) (pt x)` using `fun x hx ↦ GlobalTheory.memKL_of_push gp hL hM ((cls_eq_iff hM hM).1 rfl) (pt x) (memKL_congr (Category.id_comp t).symm x _ (hpt x).symm (memKL_of_triv_lam hL x hx))`. Establish `: Finite {x : Over.mk t ⟶ A | Triv (ev (abelian₂ A L) (fst (Over.mk t) A ≫ x) (snd (Over.mk t) A))}` using `Finite.of_injective (fun x ↦ (⟨pt x.1, hmem x.1 x.2⟩ : {y : 𝟙_ (Over (Sp k)) ⟶ B // GlobalTheory.MemKL B (L.pull (pullback.fst A.hom t)) y})) fun x y e ↦ by`.

Use `Subtype.ext (Over.OverMorphism.ext ?_)` and prove the remaining obligations. Establish `e' : pt x.1 = pt y.1` using `congrArg Subtype.val e`. Rewrite using `[← hpt x.1, ← hpt y.1, e']`. Conclude with `Set.toFinite _`.
-/
theorem kFinite : KFinite := by
  intro S A _ hA L hL hamp k _ _ t
  let B : Over (Sp k) := (Over.pullback t).obj A
  have gp : IsGrpPullback B A t (pullback.fst A.hom t) := isGrpPullback_pullback A t
  have hB : IsAbelianScheme B := PolPull.isAbelianScheme_of_isGrpPullback hA gp
  have := hA.proper
  have hM : (L.pull (pullback.fst A.hom t)).IsLB := pull_isLB hL _
  have hAmp : Out.RelAmple B (L.pull (pullback.fst A.hom t)) :=
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL hamp (IsPullback.of_hasPullback A.hom t)
  have hK := finite_memKL k B hB _ hM hAmp
  have hw : ∀ x : Over.mk t ⟶ A, x.left ≫ A.hom = 𝟙 (Sp k) ≫ t := fun x ↦ by
    rw [Over.w x, Category.id_comp]; rfl
  let pt : (Over.mk t ⟶ A) → (𝟙_ (Over (Sp k)) ⟶ B) := fun x ↦ GlobalTheory.AbDual.liftPt gp (𝟙 _) x.left (hw x)
  have hpt : ∀ x, (pt x).left ≫ pullback.fst A.hom t = x.left := fun x ↦
    GlobalTheory.AbDual.liftPt_left gp _ _ _
  have hmem : ∀ x : Over.mk t ⟶ A, Triv (ev (abelian₂ A L) (fst (Over.mk t) A ≫ x) (snd (Over.mk t) A)) →
      GlobalTheory.MemKL B (L.pull (pullback.fst A.hom t)) (pt x) := fun x hx ↦
    GlobalTheory.memKL_of_push gp hL hM ((cls_eq_iff hM hM).1 rfl) (pt x)
      (memKL_congr (Category.id_comp t).symm x _ (hpt x).symm (memKL_of_triv_lam hL x hx))
  have : Finite {x : Over.mk t ⟶ A | Triv (ev (abelian₂ A L) (fst (Over.mk t) A ≫ x) (snd (Over.mk t) A))} :=
    Finite.of_injective
      (fun x ↦ (⟨pt x.1, hmem x.1 x.2⟩ : {y : 𝟙_ (Over (Sp k)) ⟶ B //
        GlobalTheory.MemKL B (L.pull (pullback.fst A.hom t)) y})) fun x y e ↦ by
      refine Subtype.ext (Over.OverMorphism.ext ?_)
      have e' : pt x.1 = pt y.1 := congrArg Subtype.val e
      rw [← hpt x.1, ← hpt y.1, e']
  exact Set.toFinite _

end GlobalTheory.CompanionTheory.KLFinite

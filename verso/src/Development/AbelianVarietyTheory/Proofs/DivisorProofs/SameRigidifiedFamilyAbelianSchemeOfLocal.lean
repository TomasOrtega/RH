import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyTrivialOfIsoPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SurjectiveAppOfIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.SameLocal

/- English proof (translation)
Establish `hi : IsIso ((e ≫ p).app V)`. Rewrite using `[Scheme.Hom.congr_app he V]`. Conclude with `@IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance (Functor.map_isIso _ _)`. Establish `k : ∀ z, ((e ≫ p).app V).hom z = (e.app (p ⁻¹ᵁ V)).hom ((p.app V).hom z)` using `fun z => rfl`. Introduce `x x' hx`.

Apply `(ConcreteCategory.bijective_of_isIso ((e ≫ p).app V)).1` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `((e ≫ p).app V).hom x = ((e ≫ p).app V).hom x'`. Rewrite using `[k, k, hx]`.
-/
theorem injective_app_of_section {X Y : Scheme.{0}} (p : X ⟶ Y) (e : Y ⟶ X) (he : e ≫ p = 𝟙 Y)
    (V : Y.Opens) : Function.Injective (p.app V).hom := by
  have hi : IsIso ((e ≫ p).app V) := by
    rw [Scheme.Hom.congr_app he V]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance (Functor.map_isIso _ _)
  have k : ∀ z, ((e ≫ p).app V).hom z = (e.app (p ⁻¹ᵁ V)).hom ((p.app V).hom z) := fun z => rfl
  intro x x' hx
  apply (ConcreteCategory.bijective_of_isIso ((e ≫ p).app V)).1
  change ((e ≫ p).app V).hom x = ((e ≫ p).app V).hom x'
  rw [k, k, hx]

/- English proof (translation)
Introduce `R _ _ A _ hA U T M N hM hN hMr hNr Y u t hloc`. Set `p` to `(snd A Y).left`. Set `e` to `(lift (1 : Y ⟶ A) (𝟙 Y)).left`. Establish `he : e ≫ p = 𝟙 Y.left`. Simplify using `only [p, e, ← Over.comp_left, lift_snd, Over.id_left]`.

Establish `hp : ∀ V : Y.left.Opens, Function.Bijective (p.app V).hom` using `fun V => ⟨injective_app_of_section p e he V, GlobalTheory.surjective_app_of_isAbelianScheme GlobalTheory.SemiRigid.globalFns _ (Out.TLinPf.isAb_pullback Y.hom A hA) V⟩`. Rewrite using `[same_iff hM hN, ← sub_eq_zero]`. Take `⟨L, hL, hLc⟩` from `cls_surj (evc hM (fst A Y) (snd A Y ≫ u) - evc hN (fst A Y) (snd A Y ≫ t))`. Establish `hloc' : ∀ y : Y.left, ∃ V : Y.left.Opens, y ∈ V ∧ ∃ g : LB.Gen (L.pull (p ⁻¹ᵁ V).ι), g.IsGen`. Introduce `y`.

Take `⟨W, hyW, hW⟩` from `hloc y`. Use `⟨W, hyW, (cls_eq_zero_iff (pull_isLB hL _)).1 ?_⟩` and prove the remaining obligations. Rewrite using `[cls_pull hL, hLc]`. Set `j : Over.mk (W.ι ≫ Y.hom) ⟶ Y` to `Over.homMk W.ι rfl`. Establish `h0 : CechPic.pull (A ◁ j).left (evc hM (fst A Y) (snd A Y ≫ u) - evc hN (fst A Y) (snd A Y ≫ t)) = 0`.

Rewrite using `[map_sub, pull_evc, pull_evc, whiskerLeft_fst, whiskerLeft_snd_assoc, whiskerLeft_snd_assoc, sub_eq_zero]`. Conclude with `(same_iff hM hN _ _).1 hW`. Set `P : Over (Sp R)` to `Over.mk ((p ⁻¹ᵁ W).ι ≫ (A ⊗ Y).hom)`. Set `k : P ⟶ A ⊗ Y` to `Over.homMk (p ⁻¹ᵁ W).ι rfl`. Establish `hr : Set.range ((p ⁻¹ᵁ W).ι ≫ p) ⊆ Set.range W.ι`.

Introduce and unpack `_ ⟨z, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `z.2`. Set `w : P ⟶ Over.mk (W.ι ≫ Y.hom)` to `Over.homMk (IsOpenImmersion.lift W.ι ((p ⁻¹ᵁ W).ι ≫ p) hr) (by`. Simplify using `only [Over.mk_hom, P]`.

Rewrite using `[← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, Over.w (snd A Y)])`. Set `φ : P ⟶ A ⊗ Over.mk (W.ι ≫ Y.hom)` to `lift (k ≫ fst A Y) w`. Establish `hφ : φ ≫ (A ◁ j) = k`. Use `CartesianMonoidalCategory.hom_ext _ _ ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, whiskerLeft_fst, lift_fst]`.

Rewrite using `[Category.assoc, whiskerLeft_snd, lift_snd_assoc]`. Conclude with `Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)`. Establish `e2 : (p ⁻¹ᵁ W).ι = φ.left ≫ (A ◁ j).left` using `by rw [← Over.comp_left, hφ]; rfl`. Rewrite using `[e2, pull_comp, h0, map_zero]`. Take `⟨N', hN', w, hw⟩` from `GlobalTheory.CubeLawCompare.iso_pull_of_locally_trivial p hp hL hloc'`.

Establish `h1 : CechPic.pull p (cls N' hN') = cls L hL`. Rewrite using `[← cls_pull hN' p (pull_isLB hN' p)]`. Conclude with `(cls_eq_iff _ hL).2 ⟨w, hw⟩`. Establish `h2 : CechPic.pull e (cls L hL) = 0`. Rewrite using `[hLc, map_sub, pull_evc, pull_evc, lift_fst, lift_snd_assoc, Category.id_comp, hMr, hNr, sub_zero]`.

Establish `h3 : cls N' hN' = 0`. Rewrite using `[← h2, ← h1, ← pull_comp, he, pull_id]`. Rewrite using `[← hLc, ← h1, h3, map_zero]`.
-/
theorem same_of_local : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (U T : Over (Sp R)) (M : LB (A ⊗ U).left) (N : LB (A ⊗ T).left) (hM : M.IsLB) (hN : N.IsLB), (∀ (Y : Over (Sp R)) (u : Y ⟶ U), evc hM (1 : Y ⟶ A) u = 0) → (∀ (Y : Over (Sp R)) (t : Y ⟶ T), evc hN (1 : Y ⟶ A) t = 0) → ∀ (Y : Over (Sp R)) (u : Y ⟶ U) (t : Y ⟶ T), (∀ y : Y.left, ∃ W : Y.left.Opens, y ∈ W ∧ Same A M N (Over.homMk W.ι rfl ≫ u : Over.mk (W.ι ≫ Y.hom) ⟶ U) (Over.homMk W.ι rfl ≫ t)) → Same A M N u t := by
  intro R _ _ A _ hA U T M N hM hN hMr hNr Y u t hloc
  let p := (snd A Y).left
  let e := (lift (1 : Y ⟶ A) (𝟙 Y)).left
  have he : e ≫ p = 𝟙 Y.left := by
    simp only [p, e, ← Over.comp_left, lift_snd, Over.id_left]
  have hp : ∀ V : Y.left.Opens, Function.Bijective (p.app V).hom := fun V =>
    ⟨injective_app_of_section p e he V,
      GlobalTheory.surjective_app_of_isAbelianScheme GlobalTheory.SemiRigid.globalFns _ (Out.TLinPf.isAb_pullback Y.hom A hA) V⟩
  rw [same_iff hM hN, ← sub_eq_zero]
  obtain ⟨L, hL, hLc⟩ := cls_surj (evc hM (fst A Y) (snd A Y ≫ u) - evc hN (fst A Y) (snd A Y ≫ t))
  have hloc' : ∀ y : Y.left, ∃ V : Y.left.Opens, y ∈ V ∧ ∃ g : LB.Gen (L.pull (p ⁻¹ᵁ V).ι), g.IsGen := by
    intro y
    obtain ⟨W, hyW, hW⟩ := hloc y
    refine ⟨W, hyW, (cls_eq_zero_iff (pull_isLB hL _)).1 ?_⟩
    rw [cls_pull hL, hLc]
    let j : Over.mk (W.ι ≫ Y.hom) ⟶ Y := Over.homMk W.ι rfl
    have h0 : CechPic.pull (A ◁ j).left
        (evc hM (fst A Y) (snd A Y ≫ u) - evc hN (fst A Y) (snd A Y ≫ t)) = 0 := by
      rw [map_sub, pull_evc, pull_evc, whiskerLeft_fst, whiskerLeft_snd_assoc, whiskerLeft_snd_assoc, sub_eq_zero]
      exact (same_iff hM hN _ _).1 hW
    let P : Over (Sp R) := Over.mk ((p ⁻¹ᵁ W).ι ≫ (A ⊗ Y).hom)
    let k : P ⟶ A ⊗ Y := Over.homMk (p ⁻¹ᵁ W).ι rfl
    have hr : Set.range ((p ⁻¹ᵁ W).ι ≫ p) ⊆ Set.range W.ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact z.2
    let w : P ⟶ Over.mk (W.ι ≫ Y.hom) := Over.homMk (IsOpenImmersion.lift W.ι ((p ⁻¹ᵁ W).ι ≫ p) hr) (by
      simp only [Over.mk_hom, P]
      rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, Over.w (snd A Y)])
    let φ : P ⟶ A ⊗ Over.mk (W.ι ≫ Y.hom) := lift (k ≫ fst A Y) w
    have hφ : φ ≫ (A ◁ j) = k := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · rw [Category.assoc, whiskerLeft_fst, lift_fst]
      · rw [Category.assoc, whiskerLeft_snd, lift_snd_assoc]
        exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
    have e2 : (p ⁻¹ᵁ W).ι = φ.left ≫ (A ◁ j).left := by rw [← Over.comp_left, hφ]; rfl
    rw [e2, pull_comp, h0, map_zero]
  obtain ⟨N', hN', w, hw⟩ := GlobalTheory.CubeLawCompare.iso_pull_of_locally_trivial p hp hL hloc'
  have h1 : CechPic.pull p (cls N' hN') = cls L hL := by
    rw [← cls_pull hN' p (pull_isLB hN' p)]
    exact (cls_eq_iff _ hL).2 ⟨w, hw⟩
  have h2 : CechPic.pull e (cls L hL) = 0 := by
    rw [hLc, map_sub, pull_evc, pull_evc, lift_fst, lift_snd_assoc, Category.id_comp, hMr, hNr, sub_zero]
  have h3 : cls N' hN' = 0 := by
    rw [← h2, ← h1, ← pull_comp, he, pull_id]
  rw [← hLc, ← h1, h3, map_zero]

end GlobalTheory.DualCon.SameLocal

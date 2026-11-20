import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TheoremOfCubeTwoProjectiveFactors
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

/- English proof (translation)
Set `T : Over S` to `Over.mk (V.ι ≫ Y.hom)`. Set `j : T ⟶ Y` to `Over.homMk V.ι rfl`. Set `m : (A ⊗ T).left ⟶ (A ⊗ Y).left` to `(lift (fst A T) (snd A T ≫ j)).left`. Establish `hT : IsPullback (fst A T).left (snd A T).left A.hom (V.ι ≫ Y.hom)` using `IsPullback.of_hasPullback _ _`. Establish `hY : IsPullback (fst A Y).left (snd A Y).left A.hom Y.hom` using `IsPullback.of_hasPullback _ _`.

Establish `m₁ : m ≫ (fst A Y).left = (fst A T).left`. Rewrite using `[← Over.comp_left, lift_fst]`. Establish `m₂ : m ≫ (snd A Y).left = (snd A T).left ≫ V.ι`. Rewrite using `[← Over.comp_left, lift_snd, Over.comp_left]`. Both sides reduce to the same expression.

Establish `H : IsPullback m (snd A T).left (snd A Y).left V.ι` using `IsPullback.of_right (by rw [m₁]; exact hT) m₂ hY`. Set `e` to `IsPullback.isoIsPullback _ _ (isPullback_morphismRestrict (snd A Y).left V) H.flip`. Establish `he : e.hom ≫ (snd A T).left = (snd A Y).left ∣_ V` using `IsPullback.isoIsPullback_hom_fst _ _ _ _`. Establish `hq : Function.Surjective (snd A T).left.appTop.hom` using `surj_snd GlobalTheory.SemiRigid.globalFns hA T`. Establish `hi : Function.Surjective e.hom.appTop.hom`.

Establish `: IsIso (e.hom.app ⊤)` using `inferInstance`. Conclude with `(ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).2`. Rewrite using `[← he]`. Conclude with `surj_comp hi hq`.
-/
theorem surj_restrict_snd {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) (Y : Over S)
    (V : Y.left.Opens) : Function.Surjective ((snd A Y).left ∣_ V).appTop.hom := by
  let T : Over S := Over.mk (V.ι ≫ Y.hom)
  let j : T ⟶ Y := Over.homMk V.ι rfl
  let m : (A ⊗ T).left ⟶ (A ⊗ Y).left := (lift (fst A T) (snd A T ≫ j)).left
  have hT : IsPullback (fst A T).left (snd A T).left A.hom (V.ι ≫ Y.hom) := IsPullback.of_hasPullback _ _
  have hY : IsPullback (fst A Y).left (snd A Y).left A.hom Y.hom := IsPullback.of_hasPullback _ _
  have m₁ : m ≫ (fst A Y).left = (fst A T).left := by
    rw [← Over.comp_left, lift_fst]
  have m₂ : m ≫ (snd A Y).left = (snd A T).left ≫ V.ι := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]; rfl
  have H : IsPullback m (snd A T).left (snd A Y).left V.ι :=
    IsPullback.of_right (by rw [m₁]; exact hT) m₂ hY
  let e := IsPullback.isoIsPullback _ _ (isPullback_morphismRestrict (snd A Y).left V) H.flip
  have he : e.hom ≫ (snd A T).left = (snd A Y).left ∣_ V := IsPullback.isoIsPullback_hom_fst _ _ _ _
  have hq : Function.Surjective (snd A T).left.appTop.hom := surj_snd GlobalTheory.SemiRigid.globalFns hA T
  have hi : Function.Surjective e.hom.appTop.hom := by
    have : IsIso (e.hom.app ⊤) := inferInstance
    exact (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).2
  rw [← he]
  exact surj_comp hi hq

/- English proof (translation)
Introduce `S A T U _ hA N M hN hM Y y u loc`. Rewrite using `[same_iff hN.isLB hM.isLB]`. Rewrite using `[← sub_eq_zero]`. Take `⟨L, hL, hc⟩` from `cls_surj (evc hN.isLB (fst A Y) (snd A Y ≫ y) - evc hM.isLB (fst A Y) (snd A Y ≫ u))`. Rewrite using `[← hc]`.

Establish `key : ∀ {X : Scheme.{0}} (f : X ⟶ (A ⊗ Y).left), Triv (L.pull f) ↔ CechPic.pull f (evc hN.isLB (fst A Y) (snd A Y ≫ y)) = CechPic.pull f (evc hM.isLB (fst A Y) (snd A Y ≫ u))`. Introduce `X f`. Rewrite using `[← sub_eq_zero, ← map_sub, ← hc, ← cls_pull hL f (pull_isLB hL f)]`. Conclude with `(cls_eq_zero_iff (pull_isLB hL f)).symm`. Use `(cls_eq_zero_iff hL).2 (CubeGlue.triv_of_locally_triv hL (snd A Y).left (lift 1 (𝟙 Y)).left ?_ (surj_restrict_snd hA Y) ?_ ?_)` and prove the remaining obligations.

Rewrite using `[← Over.comp_left, lift_snd, Over.id_left]`. Rewrite using `[key]`. Simplify using `only [pull_evc, lift_fst, lift_snd_assoc, Category.id_comp]`. Rewrite using `[hN.add.evc_one hN.isLB, hM.add.evc_one hM.isLB]`. Introduce `p`.

Take `⟨Z, z, hz, ⟨q, hq⟩, hs⟩` from `loc p`. Use `⟨z.left.opensRange, ⟨q, hq⟩, ?_⟩` and prove the remaining obligations. Set `V` to `(snd A Y).left ⁻¹ᵁ z.left.opensRange`. Set `X' : Over S` to `Over.mk (V.ι ≫ (A ⊗ Y).hom)`. Set `i : X' ⟶ A ⊗ Y` to `Over.homMk V.ι rfl`.

Establish `hr : Set.range (i ≫ snd A Y).left ⊆ Set.range z.left`. Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `w.2`. Set `t : X' ⟶ Z` to `Over.homMk (IsOpenImmersion.lift z.left (i ≫ snd A Y).left hr) (by`. Rewrite using `[← Over.w z, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w])`.

Establish `ht : t ≫ z = i ≫ snd A Y` using `by ext1; exact IsOpenImmersion.lift_fac _ _ _`. Rewrite `hs` using `[same_iff hN.isLB hM.isLB]`. Establish `e` using `congrArg (CechPic.pull (lift (i ≫ fst A Y) t).left) hs`. Simplify using `only [pull_evc, lift_fst, lift_snd_assoc] at e`. Rewrite `e` using `[← Category.assoc t z y, ← Category.assoc t z u, ht, Category.assoc, Category.assoc]`.

Use `show Triv (L.pull i.left)`. Rewrite using `[key, pull_evc, pull_evc]`. Conclude with `e`.
-/
theorem same_of_local : ∀ (S : Scheme.{0}) (A T U : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left), Fam A N → Fam A M → ∀ (Y : Over S) (y : Y ⟶ T) (u : Y ⟶ U),
    (∀ p : Y.left, ∃ (Z : Over S) (z : Z ⟶ Y), IsOpenImmersion z.left ∧ p ∈ Set.range z.left ∧
      Same A N M (z ≫ y) (z ≫ u)) → Same A N M y u := by
  intro S A T U _ hA N M hN hM Y y u loc
  rw [same_iff hN.isLB hM.isLB]
  rw [← sub_eq_zero]
  obtain ⟨L, hL, hc⟩ := cls_surj (evc hN.isLB (fst A Y) (snd A Y ≫ y) - evc hM.isLB (fst A Y) (snd A Y ≫ u))
  rw [← hc]
  have key : ∀ {X : Scheme.{0}} (f : X ⟶ (A ⊗ Y).left), Triv (L.pull f) ↔
      CechPic.pull f (evc hN.isLB (fst A Y) (snd A Y ≫ y)) = CechPic.pull f (evc hM.isLB (fst A Y) (snd A Y ≫ u)) := by
    intro X f
    rw [← sub_eq_zero, ← map_sub, ← hc, ← cls_pull hL f (pull_isLB hL f)]
    exact (cls_eq_zero_iff (pull_isLB hL f)).symm
  refine (cls_eq_zero_iff hL).2 (CubeGlue.triv_of_locally_triv hL (snd A Y).left (lift 1 (𝟙 Y)).left ?_
    (surj_restrict_snd hA Y) ?_ ?_)
  · rw [← Over.comp_left, lift_snd, Over.id_left]
  · rw [key]
    simp only [pull_evc, lift_fst, lift_snd_assoc, Category.id_comp]
    rw [hN.add.evc_one hN.isLB, hM.add.evc_one hM.isLB]
  · intro p
    obtain ⟨Z, z, hz, ⟨q, hq⟩, hs⟩ := loc p
    refine ⟨z.left.opensRange, ⟨q, hq⟩, ?_⟩
    let V := (snd A Y).left ⁻¹ᵁ z.left.opensRange
    let X' : Over S := Over.mk (V.ι ≫ (A ⊗ Y).hom)
    let i : X' ⟶ A ⊗ Y := Over.homMk V.ι rfl
    have hr : Set.range (i ≫ snd A Y).left ⊆ Set.range z.left := by
      rintro _ ⟨w, rfl⟩
      exact w.2
    let t : X' ⟶ Z := Over.homMk (IsOpenImmersion.lift z.left (i ≫ snd A Y).left hr) (by
      rw [← Over.w z, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w])
    have ht : t ≫ z = i ≫ snd A Y := by
      ext1; exact IsOpenImmersion.lift_fac _ _ _
    rw [same_iff hN.isLB hM.isLB] at hs
    have e := congrArg (CechPic.pull (lift (i ≫ fst A Y) t).left) hs
    simp only [pull_evc, lift_fst, lift_snd_assoc] at e
    rw [← Category.assoc t z y, ← Category.assoc t z u, ht, Category.assoc, Category.assoc] at e
    show Triv (L.pull i.left)
    rw [key, pull_evc, pull_evc]
    exact e

end GlobalTheory.DualCon

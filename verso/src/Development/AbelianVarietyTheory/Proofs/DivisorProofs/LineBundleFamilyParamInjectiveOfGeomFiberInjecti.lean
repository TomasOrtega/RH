import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeAdditiveFamiliesAgreeStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualInj

/- English proof (translation)
Establish `hu : FormallyUnramified f` using `TangentCrit.formallyUnramified_of_tangent f h₂`. Establish `hs : Surjective (pullback.diagonal f)`. Use `((tfae_universallyInjective f).out 1 3).1 fun (k : Type) [Field k] y y' e => ?_` and prove the remaining obligations. Set `x : Sp (AlgebraicClosure k) ⟶ Sp k` to `Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))`. Establish `: Surjective x` using `⟨fun z => ⟨(default : PrimeSpectrum (AlgebraicClosure k)), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩`.

Establish `: Epi x` using `Flat.epi_of_flat_of_surjective x`. Use `(cancel_epi x).1 (h₁ _ _ _ ?_)` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc]`. Conclude with `congrArg (x ≫ ·) e`. Establish `: IsIso (pullback.diagonal f)` using `(isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, hs⟩`.

Conclude with `(pullback.isIso_diagonal_iff f).1 this`.
-/
theorem mono_of_points_tangents {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (h₁ : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ X), y ≫ f = y' ≫ f → y = y')
    (h₂ : ∀ (k : Type) [Field k] [IsAlgClosed k] (w : Sp (DualNumber k) ⟶ X),
      w ≫ f = TangentCrit.dualBase k ≫ TangentCrit.dualPt k ≫ w ≫ f →
        w = TangentCrit.dualBase k ≫ TangentCrit.dualPt k ≫ w) : Mono f := by
  have hu : FormallyUnramified f := TangentCrit.formallyUnramified_of_tangent f h₂
  have hs : Surjective (pullback.diagonal f) := by
    refine ((tfae_universallyInjective f).out 1 3).1 fun (k : Type) [Field k] y y' e => ?_
    let x : Sp (AlgebraicClosure k) ⟶ Sp k := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
    have : Surjective x :=
      ⟨fun z => ⟨(default : PrimeSpectrum (AlgebraicClosure k)), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
    have : Epi x := Flat.epi_of_flat_of_surjective x
    refine (cancel_epi x).1 (h₁ _ _ _ ?_)
    rw [Category.assoc, Category.assoc]
    exact congrArg (x ≫ ·) e
  have : IsIso (pullback.diagonal f) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, hs⟩
  exact (pullback.isIso_diagonal_iff f).1 this

variable {S : Scheme.{0}} {A U : Over S} [GrpObj A]

/- English proof (translation)
The claim follows from `pull_isLB hM.isLB _ add := (isAdditive_iff (pull_isLB hM.isLB _)).2 fun Y a a' y => by rw [evc_ev hM.isLB, evc_ev hM.isLB, evc_ev hM.isLB] simp only [lift_fst, lift_snd_assoc] exact (isAdditive_iff hM.isLB).1 hM.add Y a a' (y ≫ t)`.
-/
theorem fam_ev {M : LB (A ⊗ U).left} (hM : Fam A M) {T : Over S} (t : T ⟶ U) :
    Fam A (ev M (fst A T) (snd A T ≫ t)) where
  isLB := pull_isLB hM.isLB _
  add := (isAdditive_iff (pull_isLB hM.isLB _)).2 fun Y a a' y => by
    rw [evc_ev hM.isLB, evc_ev hM.isLB, evc_ev hM.isLB]
    simp only [lift_fst, lift_snd_assoc]
    exact (isAdditive_iff hM.isLB).1 hM.add Y a a' (y ≫ t)

omit [GrpObj A] in

/- English proof (translation)
Rewrite using `[same_iff (pull_isLB hM _) (pull_isLB hM' _), same_iff hM hM', evc_ev hM, evc_ev hM']`. Simplify using `only [lift_fst, lift_snd_assoc, Category.assoc]`.
-/
theorem same_ev_iff {M M' : LB (A ⊗ U).left} (hM : M.IsLB) (hM' : M'.IsLB) {T Y : Over S} (t t' : T ⟶ U)
    (y : Y ⟶ T) :
    Same A (ev M (fst A T) (snd A T ≫ t)) (ev M' (fst A T) (snd A T ≫ t')) y y ↔ Same A M M' (y ≫ t) (y ≫ t') := by
  rw [same_iff (pull_isLB hM _) (pull_isLB hM' _), same_iff hM hM', evc_ev hM, evc_ev hM']
  simp only [lift_fst, lift_snd_assoc, Category.assoc]

end GlobalTheory.DualInj

namespace GlobalTheory.DualInj

/- English proof (translation)
Introduce `R _ _ A _ hA U M hU hM hF`. Establish `: LocallyOfFiniteType (U ⊗ U).hom` using `by show LocallyOfFiniteType (pullback.fst U.hom U.hom ≫ U.hom) infer_instance`. Establish `: IsLocallyNoetherian (U ⊗ U).left` using `LocallyOfFiniteType.isLocallyNoetherian (U ⊗ U).hom`. Take `⟨G, i, hi, hG⟩` from `GlobalTheory.T.exists_closedSubscheme_additiveFamilies_agree (Sp R) A (U ⊗ U) hA (ev M (fst A (U ⊗ U)) (snd A (U ⊗ U) ≫ fst U U)) (ev M (fst A (U ⊗ U)) (snd A (U ⊗ U) ≫ snd U U)) (fam_ev hM _) (fam_ev hM _)`. Establish `key : ∀ (Y : Over (Sp R)) (y : Y ⟶ U ⊗ U), Same A M M (y ≫ fst U U) (y ≫ snd U U) ↔ ∃ z : Y ⟶ G, z ≫ i = y` using `fun Y y => (same_ev_iff hM.isLB hM.isLB _ _ y).symm.trans (hG Y y)`.

Take `⟨δ, hδ⟩` from `(key U (lift (𝟙 U) (𝟙 U))).1 (by`. Rewrite using `[lift_fst, lift_snd]`. Conclude with `(same_iff hM.isLB hM.isLB _ _).2 rfl)`. Set `p : G.left ⟶ U.left` to `(i ≫ fst U U).left`. Establish `hp : p ≫ U.hom = G.hom` using `Over.w (i ≫ fst U U)`.

Establish `: Mono i.left` using `inferInstance`. Establish `pt : ∀ (Z : Scheme.{0}) (a b : Z ⟶ G.left) (K : Type) [Field K] [IsAlgClosed K] (t : Z ⟶ Sp K) (s : Sp K ⟶ Sp R), a ≫ p = b ≫ p → a ≫ G.hom = t ≫ s → a = b`. Introduce `Z a b K _ _ t s e es`. Set `Y : Over (Sp R)` to `Over.mk (a ≫ G.hom)`. Set `α : Y ⟶ G` to `Over.homMk a rfl`.

Set `β : Y ⟶ G` to `Over.homMk b (by show b ≫ G.hom = a ≫ G.hom`. Rewrite using `[← hp, ← Category.assoc, ← e, Category.assoc])`. Set `τ : Y ⟶ Over.mk s` to `Over.homMk t es.symm`. Establish `h1 : ∀ c0 : Y ⟶ G, c0 ≫ i ≫ fst U U = c0 ≫ i ≫ snd U U` using `fun c0 => by`. Use `hF K s Y τ _ _ ?_` and prove the remaining obligations.

Use `(key Y (c0 ≫ i)).2 ⟨c0, rfl⟩` as an intermediate fact. Simplify `this` using `only [Category.assoc]`. Establish `e1 : α ≫ i ≫ fst U U = β ≫ i ≫ fst U U`. Use `Over.OverMorphism.ext ?_` and prove the remaining obligations. Simplify `e` using `only [Over.comp_left, Over.homMk_left, α, β, p]`.

Establish `e2 : α ≫ i = β ≫ i`. Use `CartesianMonoidalCategory.hom_ext _ _ ?_ ?_` and prove the remaining obligations. Simplify `e1` using `only [Category.assoc]`. Simplify `e1` using `only [Category.assoc, ← h1 α, ← h1 β]`. Establish `e3` using `congrArg CommaMorphism.left e2`.

Simplify using `only [Over.comp_left, Over.homMk_left, α, β] at e3`. Conclude with `(cancel_mono i.left).1 e3`. Establish `: LocallyOfFiniteType p` using `by show LocallyOfFiniteType (i.left ≫ pullback.fst U.hom U.hom) infer_instance`. Establish `hmono : Mono p` using `mono_of_points_tangents p (fun k _ _ y y' e => pt _ y y' k (𝟙 _) (y ≫ G.hom) e (Category.id_comp _).symm) (fun k _ _ w hw => pt _ w _ k (TangentCrit.dualBase k) (TangentCrit.dualPt k ≫ w ≫ G.hom) hw (by`. Use `congrArg (· ≫ U.hom) hw` as an intermediate fact.

Simplify `this))` using `only [Category.assoc, hp]`. Introduce `Y u u' hs`. Take `⟨z, hz⟩` from `(key Y (lift u u')).1 (by rw [lift_fst, lift_snd]; exact hs)`. Establish `hz1 : z ≫ i ≫ fst U U = u` using `by rw [← Category.assoc, hz, lift_fst]`. Establish `hzδ : z = u ≫ δ`.

Use `Over.OverMorphism.ext ((cancel_mono p).1 ?_)` and prove the remaining obligations. Establish `e1 : (z ≫ i ≫ fst U U).left = (u ≫ δ ≫ i ≫ fst U U).left`. Rewrite using `[hz1, reassoc_of% hδ, lift_fst, Category.comp_id]`. Simplify `e1` using `only [p, Over.comp_left, Category.assoc]`. Use `symm`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem inj_of_fibInj : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → ∀ (U : Over (Sp R)) (M : LB (A ⊗ U).left), LocallyOfFiniteType U.hom → Fam A M →
      FibInj A M → Inj A M := by
  intro R _ _ A _ hA U M hU hM hF
  have : LocallyOfFiniteType (U ⊗ U).hom := by
    show LocallyOfFiniteType (pullback.fst U.hom U.hom ≫ U.hom)
    infer_instance
  have : IsLocallyNoetherian (U ⊗ U).left := LocallyOfFiniteType.isLocallyNoetherian (U ⊗ U).hom
  obtain ⟨G, i, hi, hG⟩ := GlobalTheory.T.exists_closedSubscheme_additiveFamilies_agree (Sp R) A (U ⊗ U) hA
    (ev M (fst A (U ⊗ U)) (snd A (U ⊗ U) ≫ fst U U)) (ev M (fst A (U ⊗ U)) (snd A (U ⊗ U) ≫ snd U U))
    (fam_ev hM _) (fam_ev hM _)
  have key : ∀ (Y : Over (Sp R)) (y : Y ⟶ U ⊗ U),
      Same A M M (y ≫ fst U U) (y ≫ snd U U) ↔ ∃ z : Y ⟶ G, z ≫ i = y :=
    fun Y y => (same_ev_iff hM.isLB hM.isLB _ _ y).symm.trans (hG Y y)
  obtain ⟨δ, hδ⟩ := (key U (lift (𝟙 U) (𝟙 U))).1 (by
    rw [lift_fst, lift_snd]
    exact (same_iff hM.isLB hM.isLB _ _).2 rfl)
  let p : G.left ⟶ U.left := (i ≫ fst U U).left
  have hp : p ≫ U.hom = G.hom := Over.w (i ≫ fst U U)
  have : Mono i.left := inferInstance
  have pt : ∀ (Z : Scheme.{0}) (a b : Z ⟶ G.left) (K : Type) [Field K] [IsAlgClosed K] (t : Z ⟶ Sp K)
      (s : Sp K ⟶ Sp R), a ≫ p = b ≫ p → a ≫ G.hom = t ≫ s → a = b := by
    intro Z a b K _ _ t s e es
    let Y : Over (Sp R) := Over.mk (a ≫ G.hom)
    let α : Y ⟶ G := Over.homMk a rfl
    let β : Y ⟶ G := Over.homMk b (by
      show b ≫ G.hom = a ≫ G.hom
      rw [← hp, ← Category.assoc, ← e, Category.assoc])
    let τ : Y ⟶ Over.mk s := Over.homMk t es.symm
    have h1 : ∀ c0 : Y ⟶ G, c0 ≫ i ≫ fst U U = c0 ≫ i ≫ snd U U := fun c0 => by
      refine hF K s Y τ _ _ ?_
      have := (key Y (c0 ≫ i)).2 ⟨c0, rfl⟩
      simpa only [Category.assoc] using this
    have e1 : α ≫ i ≫ fst U U = β ≫ i ≫ fst U U := by
      refine Over.OverMorphism.ext ?_
      simpa only [Over.comp_left, Over.homMk_left, α, β, p] using e
    have e2 : α ≫ i = β ≫ i := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · simpa only [Category.assoc] using e1
      · simpa only [Category.assoc, ← h1 α, ← h1 β] using e1
    have e3 := congrArg CommaMorphism.left e2
    simp only [Over.comp_left, Over.homMk_left, α, β] at e3
    exact (cancel_mono i.left).1 e3
  have : LocallyOfFiniteType p := by
    show LocallyOfFiniteType (i.left ≫ pullback.fst U.hom U.hom)
    infer_instance
  have hmono : Mono p := mono_of_points_tangents p
    (fun k _ _ y y' e => pt _ y y' k (𝟙 _) (y ≫ G.hom) e (Category.id_comp _).symm)
    (fun k _ _ w hw => pt _ w _ k (TangentCrit.dualBase k) (TangentCrit.dualPt k ≫ w ≫ G.hom) hw (by
      have := congrArg (· ≫ U.hom) hw
      simpa only [Category.assoc, hp] using this))
  intro Y u u' hs
  obtain ⟨z, hz⟩ := (key Y (lift u u')).1 (by rw [lift_fst, lift_snd]; exact hs)
  have hz1 : z ≫ i ≫ fst U U = u := by rw [← Category.assoc, hz, lift_fst]
  have hzδ : z = u ≫ δ := by
    refine Over.OverMorphism.ext ((cancel_mono p).1 ?_)
    have e1 : (z ≫ i ≫ fst U U).left = (u ≫ δ ≫ i ≫ fst U U).left := by
      rw [hz1, reassoc_of% hδ, lift_fst, Category.comp_id]
    simpa only [p, Over.comp_left, Category.assoc] using e1
  symm
  calc u' = lift u u' ≫ snd U U := (lift_snd _ _).symm
    _ = u ≫ δ ≫ i ≫ snd U U := by rw [← hz, hzδ]; simp only [Category.assoc]
    _ = u := by rw [reassoc_of% hδ, lift_snd, Category.comp_id]

end GlobalTheory.DualInj

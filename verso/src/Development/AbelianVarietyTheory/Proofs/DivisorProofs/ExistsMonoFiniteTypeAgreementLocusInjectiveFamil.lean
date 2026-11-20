import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeAdditiveFamiliesAgree
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualGraph

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

/- English proof (translation)
Rewrite using `[evc_ev hN, lift_fst, lift_snd_assoc]`.
-/
theorem evc_ev_comp {T P Y : Over S} {N : LB (A ⊗ T).left} (hN : N.IsLB) (f : P ⟶ T)
    (h : (ev N (fst A P) (snd A P ≫ f)).IsLB) (a : Y ⟶ A) (p : Y ⟶ P) : evc h a p = evc hN a (p ≫ f) := by
  rw [evc_ev hN, lift_fst, lift_snd_assoc]

/- English proof (translation)
Establish `h : (ev N (fst A P) (snd A P ≫ f)).IsLB` using `pull_isLB hN.isLB _`. Use `⟨h, (isAdditive_iff h).2 fun Y a a' p ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[evc_ev_comp hN.isLB f h, evc_ev_comp hN.isLB f h, evc_ev_comp hN.isLB f h]`. Conclude with `(isAdditive_iff hN.isLB).1 hN.add Y a a' (p ≫ f)`.
-/
theorem fam_ev {T P : Over S} {N : LB (A ⊗ T).left} (hN : Fam A N) (f : P ⟶ T) :
    Fam A (ev N (fst A P) (snd A P ≫ f)) := by
  have h : (ev N (fst A P) (snd A P ≫ f)).IsLB := pull_isLB hN.isLB _
  refine ⟨h, (isAdditive_iff h).2 fun Y a a' p ↦ ?_⟩
  rw [evc_ev_comp hN.isLB f h, evc_ev_comp hN.isLB f h, evc_ev_comp hN.isLB f h]
  exact (isAdditive_iff hN.isLB).1 hN.add Y a a' (p ≫ f)

/- English proof (translation)
Establish `h₁ : (ev N (fst A (T ⊗ U)) (snd A (T ⊗ U) ≫ fst T U)).IsLB` using `pull_isLB hN _`. Establish `h₂ : (ev M (fst A (T ⊗ U)) (snd A (T ⊗ U) ≫ snd T U)).IsLB` using `pull_isLB hM _`. Rewrite using `[same_iff h₁ h₂, same_iff hN hM, evc_ev_comp hN _ h₁, evc_ev_comp hM _ h₂, Category.assoc, Category.assoc]`.
-/
theorem same_prod_iff {T U Y : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB) (hM : M.IsLB)
    (p : Y ⟶ T ⊗ U) :
    Same A (ev N (fst A (T ⊗ U)) (snd A (T ⊗ U) ≫ fst T U)) (ev M (fst A (T ⊗ U)) (snd A (T ⊗ U) ≫ snd T U)) p p ↔
      Same A N M (p ≫ fst T U) (p ≫ snd T U) := by
  have h₁ : (ev N (fst A (T ⊗ U)) (snd A (T ⊗ U) ≫ fst T U)).IsLB := pull_isLB hN _
  have h₂ : (ev M (fst A (T ⊗ U)) (snd A (T ⊗ U) ≫ snd T U)).IsLB := pull_isLB hM _
  rw [same_iff h₁ h₂, same_iff hN hM, evc_ev_comp hN _ h₁, evc_ev_comp hM _ h₂, Category.assoc, Category.assoc]

/- English proof (translation)
Introduce `S A _ hA T U _ _ N M hN hM hI`. Establish `hf : LocallyOfFiniteType (fst T U).left` using `by show LocallyOfFiniteType (pullback.fst T.hom U.hom) infer_instance`. Use `haveI : IsLocallyNoetherian (T ⊗ U).left := LocallyOfFiniteType.isLocallyNoetherian (fst T U).left`. Take `⟨G, i, hi, hG⟩` from `GlobalTheory.DualLocus.exists_closed_same S A (T ⊗ U) hA _ _ (fam_ev hN (fst T U)) (fam_ev hM (snd T U))`. Establish `key : ∀ (Y : Over S) (z : Y ⟶ G), Same A N M (z ≫ i ≫ fst T U) (z ≫ i ≫ snd T U)` using `fun Y z ↦ by`.

Rewrite using `[← Category.assoc, ← Category.assoc, ← same_prod_iff hN.isLB hM.isLB]`. Conclude with `(hG Y (z ≫ i)).2 ⟨z, rfl⟩`. Establish `hw : i.left ≫ (fst T U).left ≫ T.hom = G.hom`. Rewrite using `[Over.w (fst T U), Over.w i]`. Use `⟨G, i ≫ fst T U, ⟨fun {W} a b hab ↦ ?_⟩, ?_, fun Y y ↦ ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Set `Y : Over S` to `Over.mk (a ≫ G.hom)`. Set `a' : Y ⟶ G` to `Over.homMk a rfl`. Set `b' : Y ⟶ G` to `Over.homMk b (by show b ≫ G.hom = a ≫ G.hom`. Simplify using `only [Over.comp_left] at hab`. Rewrite using `[← hw, reassoc_of% hab])`.

Establish `e₁ : a' ≫ i ≫ fst T U = b' ≫ i ≫ fst T U` using `Over.OverMorphism.ext (by`. Simplify `hab)` using `only [Over.comp_left, a', b', Over.homMk_left]`. Establish `e₂ : a' ≫ i ≫ snd T U = b' ≫ i ≫ snd T U`. Use `hI Y _ _ ((same_iff hM.isLB hM.isLB _ _).2 ?_)` and prove the remaining obligations. Rewrite using `[← (same_iff hN.isLB hM.isLB _ _).1 (key Y a'), ← (same_iff hN.isLB hM.isLB _ _).1 (key Y b'), e₁]`.

Establish `e : a' ≫ i = b' ≫ i`. Rewrite `e₁`, `e₂` using `[← Category.assoc, ← Category.assoc]`. Conclude with `CartesianMonoidalCategory.hom_ext _ _ e₁ e₂`. Establish `e'` using `congrArg (fun q : Y ⟶ T ⊗ U ↦ q.left) e`. Simplify using `only [Over.comp_left, a', b', Over.homMk_left] at e'`.

Conclude with `(cancel_mono i.left).1 e'`. Rewrite using `[Over.comp_left] infer_instance`. Introduce and unpack `⟨u, hu⟩`. Establish `hs` using `(same_prod_iff hN.isLB hM.isLB (lift y u)).2 (by rwa [lift_fst, lift_snd])`. Take `⟨z, hz⟩` from `(hG Y (lift y u)).1 hs`.

Use `⟨z.left, ?_⟩` and prove the remaining obligations. Rewrite using `[← Over.comp_left, ← Category.assoc, hz, lift_fst]`. Introduce and unpack `⟨z, hz⟩`. Set `z' : Y ⟶ G` to `Over.homMk z (by show z ≫ G.hom = Y.hom`. Rewrite using `[← hw, ← Over.w y, ← hz, Over.comp_left]`.

Simplify using `only [Category.assoc])`. Establish `ey : z' ≫ i ≫ fst T U = y` using `Over.OverMorphism.ext (by`. Simplify `hz)` using `only [Over.comp_left, z', Over.homMk_left]`. Use `⟨z' ≫ i ≫ snd T U, ?_⟩` and prove the remaining obligations. Use `key Y z'` as an intermediate fact.

Rewrite `this` using `[ey]`. Then use the resulting hypothesis.
-/
theorem exists_mono_same : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (T U : Over S) [IsLocallyNoetherian T.left] [LocallyOfFiniteType U.hom] (N : LB (A ⊗ T).left)
      (M : LB (A ⊗ U).left), Fam A N → Fam A M → Inj A M → ∃ (G : Over S) (π : G ⟶ T), Mono π.left ∧
        LocallyOfFiniteType π.left ∧ ∀ (Y : Over S) (y : Y ⟶ T),
          (∃ u : Y ⟶ U, Same A N M y u) ↔ ∃ z : Y.left ⟶ G.left, z ≫ π.left = y.left := by
  intro S A _ hA T U _ _ N M hN hM hI
  have hf : LocallyOfFiniteType (fst T U).left := by
    show LocallyOfFiniteType (pullback.fst T.hom U.hom)
    infer_instance
  haveI : IsLocallyNoetherian (T ⊗ U).left := LocallyOfFiniteType.isLocallyNoetherian (fst T U).left
  obtain ⟨G, i, hi, hG⟩ := GlobalTheory.DualLocus.exists_closed_same S A (T ⊗ U) hA _ _ (fam_ev hN (fst T U))
    (fam_ev hM (snd T U))
  have key : ∀ (Y : Over S) (z : Y ⟶ G), Same A N M (z ≫ i ≫ fst T U) (z ≫ i ≫ snd T U) := fun Y z ↦ by
    rw [← Category.assoc, ← Category.assoc, ← same_prod_iff hN.isLB hM.isLB]
    exact (hG Y (z ≫ i)).2 ⟨z, rfl⟩
  have hw : i.left ≫ (fst T U).left ≫ T.hom = G.hom := by
    rw [Over.w (fst T U), Over.w i]
  refine ⟨G, i ≫ fst T U, ⟨fun {W} a b hab ↦ ?_⟩, ?_, fun Y y ↦ ⟨?_, ?_⟩⟩
  · let Y : Over S := Over.mk (a ≫ G.hom)
    let a' : Y ⟶ G := Over.homMk a rfl
    let b' : Y ⟶ G := Over.homMk b (by
      show b ≫ G.hom = a ≫ G.hom
      simp only [Over.comp_left] at hab
      rw [← hw, reassoc_of% hab])
    have e₁ : a' ≫ i ≫ fst T U = b' ≫ i ≫ fst T U := Over.OverMorphism.ext (by
      simpa only [Over.comp_left, a', b', Over.homMk_left] using hab)
    have e₂ : a' ≫ i ≫ snd T U = b' ≫ i ≫ snd T U := by
      refine hI Y _ _ ((same_iff hM.isLB hM.isLB _ _).2 ?_)
      rw [← (same_iff hN.isLB hM.isLB _ _).1 (key Y a'), ← (same_iff hN.isLB hM.isLB _ _).1 (key Y b'), e₁]
    have e : a' ≫ i = b' ≫ i := by
      rw [← Category.assoc, ← Category.assoc] at e₁ e₂
      exact CartesianMonoidalCategory.hom_ext _ _ e₁ e₂
    have e' := congrArg (fun q : Y ⟶ T ⊗ U ↦ q.left) e
    simp only [Over.comp_left, a', b', Over.homMk_left] at e'
    exact (cancel_mono i.left).1 e'
  · rw [Over.comp_left]
    infer_instance
  · rintro ⟨u, hu⟩
    have hs := (same_prod_iff hN.isLB hM.isLB (lift y u)).2 (by rwa [lift_fst, lift_snd])
    obtain ⟨z, hz⟩ := (hG Y (lift y u)).1 hs
    refine ⟨z.left, ?_⟩
    rw [← Over.comp_left, ← Category.assoc, hz, lift_fst]
  · rintro ⟨z, hz⟩
    let z' : Y ⟶ G := Over.homMk z (by
      show z ≫ G.hom = Y.hom
      rw [← hw, ← Over.w y, ← hz, Over.comp_left]
      simp only [Category.assoc])
    have ey : z' ≫ i ≫ fst T U = y := Over.OverMorphism.ext (by
      simpa only [Over.comp_left, z', Over.homMk_left] using hz)
    refine ⟨z' ≫ i ≫ snd T U, ?_⟩
    have := key Y z'
    rwa [ey] at this

end GlobalTheory.DualGraph

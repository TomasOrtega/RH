import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

/- English proof (translation)
Establish `h : (ev N (fst A Y) (snd A Y ≫ y)).IsLB` using `pull_isLB hN.isLB _`. Use `⟨h, (isAdditive_iff h).2 fun Z a a' t ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[evc_ev hN.isLB, evc_ev hN.isLB, evc_ev hN.isLB]`. Simplify using `only [lift_fst, lift_snd_assoc]`. Conclude with `(isAdditive_iff hN.isLB).1 hN.add Z a a' (t ≫ y)`.
-/
theorem fam_ev_param {S : Scheme.{0}} {A T Y : Over S} [GrpObj A] {N : LB (A ⊗ T).left} (hN : Fam A N)
    (y : Y ⟶ T) : Fam A (ev N (fst A Y) (snd A Y ≫ y)) := by
  have h : (ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB hN.isLB _
  refine ⟨h, (isAdditive_iff h).2 fun Z a a' t ↦ ?_⟩
  rw [evc_ev hN.isLB, evc_ev hN.isLB, evc_ev hN.isLB]
  simp only [lift_fst, lift_snd_assoc]
  exact (isAdditive_iff hN.isLB).1 hN.add Z a a' (t ≫ y)

/- English proof (translation)
Introduce `S A B S' U _ b P M hP hM hI`. Take `⟨φ, ⟨hb, hN⟩, -⟩` from `hP.univ (U ⊗ S') (snd U S') _ (fam_ev_param hM (fst U S'))`. Establish `hS : Same A M P (fst U S') φ` using `hN`. Use `⟨φ, hb, hS, ?_⟩` and prove the remaining obligations. Establish `hm : Mono φ` using `⟨fun {Y} a a' e ↦ by`.

Establish `e1 : Same A M P (a ≫ fst U S') (a ≫ φ)`. Rewrite `hS`, the goal using `[same_iff hM.isLB hP.fam.isLB]`. Use `congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ a)).left) hS` as an intermediate fact. Simplify `this` using `only [pull_evc, lift_fst, lift_snd_assoc, Category.assoc]`. Establish `e2 : Same A M P (a' ≫ fst U S') (a' ≫ φ)`.

Rewrite `hS`, the goal using `[same_iff hM.isLB hP.fam.isLB]`. Use `congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ a')).left) hS` as an intermediate fact. Simplify `this` using `only [pull_evc, lift_fst, lift_snd_assoc, Category.assoc]`. Establish `e3 : Same A M M (a ≫ fst U S') (a' ≫ fst U S')`. Rewrite `e1`, `e2` using `[same_iff hM.isLB hP.fam.isLB]`.

Rewrite using `[same_iff hM.isLB hM.isLB, e1, e2, e]`. Establish `ef` using `hI Y _ _ e3`. Establish `es : a ≫ snd U S' = a' ≫ snd U S'` using `by rw [← hb, reassoc_of% e]`. Conclude with `CartesianMonoidalCategory.hom_ext _ _ ef es⟩`. Conclude with `Over.mono_left_of_mono φ`.
-/
theorem classify_mono : ∀ (S : Scheme.{0}) (A B S' U : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left)
    (M : LB (A ⊗ U).left), Rep A b P → Fam A M → Inj A M →
    ∃ φ : U ⊗ S' ⟶ B, φ ≫ b = snd U S' ∧ Same A M P (fst U S') φ ∧ Mono φ.left := by
  intro S A B S' U _ b P M hP hM hI
  obtain ⟨φ, ⟨hb, hN⟩, -⟩ := hP.univ (U ⊗ S') (snd U S') _ (fam_ev_param hM (fst U S'))
  have hS : Same A M P (fst U S') φ := hN
  refine ⟨φ, hb, hS, ?_⟩
  have hm : Mono φ := ⟨fun {Y} a a' e ↦ by
    have e1 : Same A M P (a ≫ fst U S') (a ≫ φ) := by
      rw [same_iff hM.isLB hP.fam.isLB] at hS ⊢
      have := congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ a)).left) hS
      simpa only [pull_evc, lift_fst, lift_snd_assoc, Category.assoc] using this
    have e2 : Same A M P (a' ≫ fst U S') (a' ≫ φ) := by
      rw [same_iff hM.isLB hP.fam.isLB] at hS ⊢
      have := congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ a')).left) hS
      simpa only [pull_evc, lift_fst, lift_snd_assoc, Category.assoc] using this
    have e3 : Same A M M (a ≫ fst U S') (a' ≫ fst U S') := by
      rw [same_iff hM.isLB hP.fam.isLB] at e1 e2
      rw [same_iff hM.isLB hM.isLB, e1, e2, e]
    have ef := hI Y _ _ e3
    have es : a ≫ snd U S' = a' ≫ snd U S' := by rw [← hb, reassoc_of% e]
    exact CartesianMonoidalCategory.hom_ext _ _ ef es⟩
  exact Over.mono_left_of_mono φ

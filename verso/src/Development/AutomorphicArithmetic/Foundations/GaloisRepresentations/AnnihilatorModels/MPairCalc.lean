import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleKernelKilledByIntegerPrimeToP

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw in
/- English proof (translation)
Introduce `p _ D R _ b N S s o`. Establish `hcls : ∀ {X Y : Scheme} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X), cls (L.pull f) (pull_isLB hL f) = pull f (cls L hL)`. Introduce `X Y L hL f`. Rewrite using `[cls_linComb hL]`. Simplify using the standard rewrite rules.

Establish `move : ∀ {T : Over S} (u : T ⟶ G2 o.A) (F₁ F₂ : G2 o.A ⟶ G2 o.A), LBIso (o.P.pull F₁.left) (o.P.pull F₂.left) → pull (u ≫ F₁).left (cls o.P o.isLB) = pull (u ≫ F₂).left (cls o.P o.isLB)`. Introduce `T u F₁ F₂ h`. Rewrite using `[Over.comp_left, Over.comp_left, pull_comp, pull_comp, ← hcls o.isLB F₁.left, ← hcls o.isLB F₂.left, (cls_eq_iff _ _).2 h]`. Take `⟨e, he, k⟩` from `o.kerP`. Take `⟨t₁, h₁⟩` from `o.rig₁`.

Take `⟨t₂, h₂⟩` from `o.rig₂`. Establish `hadd` using `additive_of_cube GlobalTheory.CubeTop.cubeTheorem o.ab o.ab o.isLB ⟨t₁, h₁⟩ ⟨t₂, h₂⟩`. Use `⟨hadd.1, hadd.2, ?_, ⟨e, he, fun T x hx => k T x ((triv_ev_iff o.isLB _ _).2 hx)⟩, ?_⟩` and prove the remaining obligations. Introduce `T x y a`. Establish `h` using `move (lift x y) _ _ (o.rosati ((algebraMap (𝓞 D.F) D.O) a))`.

Rewrite `h` using `[D.star_F, MulOpposite.unop_op]`. Unfold `evc`. Apply the tactic sequence `convert h using 3 <;> simp`. Introduce `o' ψ c`. Establish `hc : cls (Hecke.lbPow o.P c) (LB.isLB_linComb o.isLB _ _) = c • cls o.P o.isLB`.

Unfold `Hecke.lbPow`. Rewrite using `[cls_linComb o.isLB]`. Simplify using `[pull_id]`. Establish `hcomp : ∀ {T : Over S} (x y : T ⟶ o.A), (lift x y).left ≫ sq2 ψ = (lift (x ≫ ψ) (y ≫ ψ)).left`. Introduce `T x y`.

Unfold `sq2`. Rewrite using `[← Over.comp_left]`. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h⟩ T x y`.

Establish `h' : cls (Hecke.lbPow o.P c) (LB.isLB_linComb o.isLB _ _) = cls (o'.P.pull (sq2 ψ)) (pull_isLB o'.isLB (sq2 ψ))` using `(cls_eq_iff _ _).2 h`. Rewrite `h'` using `[hc, hcls o'.isLB]`. Unfold `evc`. Rewrite using `[← hcomp, pull_comp, ← h', map_nsmul]`. Introduce `h`.

Use `⟨(cls_eq_iff (LB.isLB_linComb o.isLB _ _) (pull_isLB o'.isLB (sq2 ψ))).1 ?_⟩` and prove the remaining obligations. Establish `h'` using `h (G2 o.A) (fst o.A o.A) (snd o.A o.A)`. Unfold `evc at h'`. Rewrite `h'` using `[← hcomp, pull_comp]`. Simplify using `only [lift_fst_snd, Over.id_left, pull_id] at h'`.

Use `show cls (Hecke.lbPow o.P c) (LB.isLB_linComb o.isLB _ _) = cls (o'.P.pull (sq2 ψ)) (pull_isLB o'.isLB (sq2 ψ))`. Rewrite using `[hc, hcls o'.isLB, h']`.
-/
theorem UpperTheory.Gal.crystallineComparison.Mod.pairCalc_of :
    PairCalc := by
  intro p _ D R _ b N S s o
  have hcls : ∀ {X Y : Scheme} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X),
      cls (L.pull f) (pull_isLB hL f) = pull f (cls L hL) := by
    intro X Y L hL f
    rw [cls_linComb hL]
    simp
  have move : ∀ {T : Over S} (u : T ⟶ G2 o.A) (F₁ F₂ : G2 o.A ⟶ G2 o.A),
      LBIso (o.P.pull F₁.left) (o.P.pull F₂.left) →
        pull (u ≫ F₁).left (cls o.P o.isLB) = pull (u ≫ F₂).left (cls o.P o.isLB) := by
    intro T u F₁ F₂ h
    rw [Over.comp_left, Over.comp_left, pull_comp, pull_comp, ← hcls o.isLB F₁.left,
      ← hcls o.isLB F₂.left,
      (cls_eq_iff _ _).2 h]
  obtain ⟨e, he, k⟩ := o.kerP
  obtain ⟨t₁, h₁⟩ := o.rig₁
  obtain ⟨t₂, h₂⟩ := o.rig₂
  have hadd := additive_of_cube GlobalTheory.CubeTop.cubeTheorem o.ab o.ab o.isLB ⟨t₁, h₁⟩ ⟨t₂, h₂⟩
  refine ⟨hadd.1, hadd.2, ?_, ⟨e, he, fun T x hx => k T x ((triv_ev_iff o.isLB _ _).2 hx)⟩, ?_⟩
  · intro T x y a
    have h := move (lift x y) _ _ (o.rosati ((algebraMap (𝓞 D.F) D.O) a))
    rw [D.star_F, MulOpposite.unop_op] at h
    unfold evc
    convert h using 3 <;> simp
  · intro o' ψ c
    have hc : cls (Hecke.lbPow o.P c) (LB.isLB_linComb o.isLB _ _) = c • cls o.P o.isLB := by
      unfold Hecke.lbPow
      rw [cls_linComb o.isLB]
      simp [pull_id]
    have hcomp : ∀ {T : Over S} (x y : T ⟶ o.A),
        (lift x y).left ≫ sq2 ψ = (lift (x ≫ ψ) (y ≫ ψ)).left := by
      intro T x y
      unfold sq2
      rw [← Over.comp_left]
      simp
    constructor
    · rintro ⟨h⟩ T x y
      have h' : cls (Hecke.lbPow o.P c) (LB.isLB_linComb o.isLB _ _) =
          cls (o'.P.pull (sq2 ψ)) (pull_isLB o'.isLB (sq2 ψ)) :=
        (cls_eq_iff _ _).2 h
      rw [hc, hcls o'.isLB] at h'
      unfold evc
      rw [← hcomp, pull_comp, ← h', map_nsmul]
    · intro h
      refine ⟨(cls_eq_iff (LB.isLB_linComb o.isLB _ _) (pull_isLB o'.isLB (sq2 ψ))).1 ?_⟩
      have h' := h (G2 o.A) (fst o.A o.A) (snd o.A o.A)
      unfold evc at h'
      rw [← hcomp, pull_comp] at h'
      simp only [lift_fst_snd, Over.id_left, pull_id] at h'
      show cls (Hecke.lbPow o.P c) (LB.isLB_linComb o.isLB _ _) =
        cls (o'.P.pull (sq2 ψ)) (pull_isLB o'.isLB (sq2 ψ))
      rw [hc, hcls o'.isLB, h']

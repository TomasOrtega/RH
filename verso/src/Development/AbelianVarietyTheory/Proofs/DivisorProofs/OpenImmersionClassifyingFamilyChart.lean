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

namespace GlobalTheory.RepChart

/- English proof (translation)
Introduce `S A B S' U _ b P M hP hM φ hφb hsame hopen T t N hN`. Establish `hP'` using `hP.fam.isLB`. Establish `hM'` using `hM.isLB`. Establish `hN'` using `hN.isLB`. Take `⟨x, ⟨hxb, hxN⟩, -⟩` from `hP.univ T t N hN`.

Establish `ex : cls N hN' = evc hP' (fst A T) (snd A T ≫ x)` using `(cls_eq_iff hN' (pull_isLB hP' _)).2 hxN`. Establish `eφ : evc hM' (fst A (U ⊗ S')) (snd A (U ⊗ S') ≫ fst U S') = evc hP' (fst A (U ⊗ S')) (snd A (U ⊗ S') ≫ φ)` using `(same_iff hM' hP' _ _).1 hsame`. Establish `eY : ∀ (Y : Over S) (y : Y ⟶ T), evc hN' (fst A Y) (snd A Y ≫ y) = evc hP' (fst A Y) (snd A Y ≫ y ≫ x)`. Introduce `Y y`. Establish `e` using `congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ y)).left) ex`.

Rewrite `e` using `[pull_evc, lift_fst, lift_snd_assoc]`. Conclude with `e`. Establish `eV : ∀ (Y : Over S) (v : Y ⟶ U ⊗ S'), evc hM' (fst A Y) (snd A Y ≫ v ≫ fst U S') = evc hP' (fst A Y) (snd A Y ≫ v ≫ φ)`. Introduce `Y v`. Establish `e` using `congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ v)).left) eφ`.

Rewrite `e` using `[pull_evc, pull_evc, lift_fst, lift_snd_assoc, lift_snd_assoc]`. Conclude with `e`. Establish `uniq : ∀ (Y : Over S) (y : Y ⟶ T) (x₁ x₂ : Y ⟶ B), x₁ ≫ b = y ≫ t → x₂ ≫ b = y ≫ t → evc hP' (fst A Y) (snd A Y ≫ x₁) = evc hN' (fst A Y) (snd A Y ≫ y) → evc hP' (fst A Y) (snd A Y ≫ x₂) = evc hN' (fst A Y) (snd A Y ≫ y) → x₁ = x₂`. Introduce `Y y x₁ x₂ h₁ h₂ e₁ e₂`. Establish `hL : (ev N (fst A Y) (snd A Y ≫ y)).IsLB` using `pull_isLB hN' _`.

Establish `hF : Fam A (ev N (fst A Y) (snd A Y ≫ y))`. Use `⟨hL, (isAdditive_iff hL).2 fun Z a a' z ↦ ?_⟩` and prove the remaining obligations. Simplify using `only [evc_ev hN', lift_fst, lift_snd_assoc]`. Conclude with `(isAdditive_iff hN').1 hN.add Z a a' (z ≫ y)`. Use `(hP.univ Y (y ≫ t) _ hF).unique ⟨h₁, (cls_eq_iff hL (pull_isLB hP' _)).1 ?_⟩ ⟨h₂, (cls_eq_iff hL (pull_isLB hP' _)).1 ?_⟩` and prove the remaining obligations.

Rewrite using `[cls_ev hN', cls_ev hP', e₁]`. Rewrite using `[cls_ev hN', cls_ev hP', e₂]`. Use `⟨x.left ⁻¹ᵁ φ.left.opensRange, fun Y y ↦ ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨u, hu⟩`. Rewrite `hu` using `[same_iff hN' hM']`.

Set `v : Y ⟶ U ⊗ S'` to `lift u (y ≫ t)`. Establish `hvx : v ≫ φ = y ≫ x`. Use `uniq Y y _ _ ?_ ?_ ?_ (by rw [eY])` and prove the remaining obligations. Rewrite using `[Category.assoc, hφb, lift_snd]`. Rewrite using `[Category.assoc, hxb]`.

Rewrite using `[← eV, lift_fst, hu]`. Introduce `z`. Establish `e` using `congrArg (fun q : Y ⟶ B ↦ q.left z) hvx`. Simplify using `only [Over.comp_left, Scheme.Hom.comp_apply] at e`. Simplify using `only [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange]`.

Conclude with `⟨_, e⟩`. Introduce `h`. Establish `hr : Set.range (y.left ≫ x.left) ⊆ Set.range φ.left`. Introduce and unpack `_ ⟨z, rfl⟩`. Use `h z` as an intermediate fact.

Simplify using `only [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange] at this`. Simplify `this` using `[Scheme.Hom.comp_apply]`. Set `l` to `IsOpenImmersion.lift φ.left (y.left ≫ x.left) hr`. Establish `hl : l ≫ φ.left = y.left ≫ x.left` using `IsOpenImmersion.lift_fac _ _ _`. Set `v : Y ⟶ U ⊗ S'` to `Over.homMk l (by`.

Rewrite using `[← Over.w φ, ← Category.assoc, hl, Category.assoc, Over.w x, Over.w y])`. Establish `hvx : v ≫ φ = y ≫ x` using `Over.OverMorphism.ext (by simpa [v] using hl)`. Use `⟨v ≫ fst U S', (same_iff hN' hM' _ _).2 ?_⟩` and prove the remaining obligations. Rewrite using `[eV, hvx, eY]`.
-/
theorem repChart : ∀ (S : Scheme.{0}) (A B S' U : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left) (M : LB (A ⊗ U).left), Rep A b P → Fam A M → ∀ φ : U ⊗ S' ⟶ B, φ ≫ b = snd U S' → Same A M P (fst U S') φ → IsOpenImmersion φ.left → ∀ (T : Over S) (_ : T ⟶ S') (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N := by
  intro S A B S' U _ b P M hP hM φ hφb hsame hopen T t N hN
  have hP' := hP.fam.isLB
  have hM' := hM.isLB
  have hN' := hN.isLB
  obtain ⟨x, ⟨hxb, hxN⟩, -⟩ := hP.univ T t N hN
  have ex : cls N hN' = evc hP' (fst A T) (snd A T ≫ x) := (cls_eq_iff hN' (pull_isLB hP' _)).2 hxN
  have eφ : evc hM' (fst A (U ⊗ S')) (snd A (U ⊗ S') ≫ fst U S') = evc hP' (fst A (U ⊗ S')) (snd A (U ⊗ S') ≫ φ) :=
    (same_iff hM' hP' _ _).1 hsame
  have eY : ∀ (Y : Over S) (y : Y ⟶ T), evc hN' (fst A Y) (snd A Y ≫ y) = evc hP' (fst A Y) (snd A Y ≫ y ≫ x) := by
    intro Y y
    have e := congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ y)).left) ex
    rw [pull_evc, lift_fst, lift_snd_assoc] at e
    exact e
  have eV : ∀ (Y : Over S) (v : Y ⟶ U ⊗ S'), evc hM' (fst A Y) (snd A Y ≫ v ≫ fst U S') =
      evc hP' (fst A Y) (snd A Y ≫ v ≫ φ) := by
    intro Y v
    have e := congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ v)).left) eφ
    rw [pull_evc, pull_evc, lift_fst, lift_snd_assoc, lift_snd_assoc] at e
    exact e
  have uniq : ∀ (Y : Over S) (y : Y ⟶ T) (x₁ x₂ : Y ⟶ B), x₁ ≫ b = y ≫ t → x₂ ≫ b = y ≫ t →
      evc hP' (fst A Y) (snd A Y ≫ x₁) = evc hN' (fst A Y) (snd A Y ≫ y) →
      evc hP' (fst A Y) (snd A Y ≫ x₂) = evc hN' (fst A Y) (snd A Y ≫ y) → x₁ = x₂ := by
    intro Y y x₁ x₂ h₁ h₂ e₁ e₂
    have hL : (ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB hN' _
    have hF : Fam A (ev N (fst A Y) (snd A Y ≫ y)) := by
      refine ⟨hL, (isAdditive_iff hL).2 fun Z a a' z ↦ ?_⟩
      simp only [evc_ev hN', lift_fst, lift_snd_assoc]
      exact (isAdditive_iff hN').1 hN.add Z a a' (z ≫ y)
    refine (hP.univ Y (y ≫ t) _ hF).unique ⟨h₁, (cls_eq_iff hL (pull_isLB hP' _)).1 ?_⟩
      ⟨h₂, (cls_eq_iff hL (pull_isLB hP' _)).1 ?_⟩
    · rw [cls_ev hN', cls_ev hP', e₁]
    · rw [cls_ev hN', cls_ev hP', e₂]
  refine ⟨x.left ⁻¹ᵁ φ.left.opensRange, fun Y y ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨u, hu⟩
    rw [same_iff hN' hM'] at hu
    let v : Y ⟶ U ⊗ S' := lift u (y ≫ t)
    have hvx : v ≫ φ = y ≫ x := by
      refine uniq Y y _ _ ?_ ?_ ?_ (by rw [eY])
      · rw [Category.assoc, hφb, lift_snd]
      · rw [Category.assoc, hxb]
      · rw [← eV, lift_fst, hu]
    intro z
    have e := congrArg (fun q : Y ⟶ B ↦ q.left z) hvx
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at e
    simp only [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange]
    exact ⟨_, e⟩
  · intro h
    have hr : Set.range (y.left ≫ x.left) ⊆ Set.range φ.left := by
      rintro _ ⟨z, rfl⟩
      have := h z
      simp only [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange] at this
      simpa [Scheme.Hom.comp_apply] using this
    let l := IsOpenImmersion.lift φ.left (y.left ≫ x.left) hr
    have hl : l ≫ φ.left = y.left ≫ x.left := IsOpenImmersion.lift_fac _ _ _
    let v : Y ⟶ U ⊗ S' := Over.homMk l (by
      rw [← Over.w φ, ← Category.assoc, hl, Category.assoc, Over.w x, Over.w y])
    have hvx : v ≫ φ = y ≫ x := Over.OverMorphism.ext (by simpa [v] using hl)
    refine ⟨v ≫ fst U S', (same_iff hN' hM' _ _).2 ?_⟩
    rw [eV, hvx, eY]

end GlobalTheory.RepChart

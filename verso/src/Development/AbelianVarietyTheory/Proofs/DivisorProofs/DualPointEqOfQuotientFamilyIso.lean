import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

/- English proof (translation)
Introduce `p`. Establish `hD : (Out.translDiff A L (x * x'⁻¹)).IsLB` using `LB.isLB_linComb hL _ _`. Take `⟨V, hV, hc⟩` from `exists_pull_eq_zero (CechPic.pull x.left (cls L hL) - CechPic.pull x'.left (cls L hL)) p`. Use `⟨V, hV, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩` and prove the remaining obligations. Establish `e₁` using `pull_translDiff hL (x * x'⁻¹) hD (fst Z A) (snd Z A)`.

Rewrite `e₁` using `[lift_fst_snd, Over.id_left, pull_id]`. Establish `k₁ : ((fst Z A ≫ x')⁻¹ * snd Z A) * (fst Z A ≫ x) = (fst Z A ≫ (x * x'⁻¹)) * snd Z A`. Rewrite using `[MonObj.comp_mul, GrpObj.comp_inv, mul_comm _ (fst Z A ≫ x)]`. Conclude with `(_root_.mul_assoc _ _ _).symm`. Establish `k₂ : ((fst Z A ≫ x')⁻¹ * snd Z A) * (fst Z A ≫ x') = snd Z A`.

Rewrite using `[mul_comm, mul_inv_cancel_left]`. Establish `e₃` using `h (Z ⊗ A) ((fst Z A ≫ x')⁻¹ * snd Z A) (fst Z A)`. Rewrite `e₃` using `[k₁, k₂]`. Establish `e₂ : cls _ hD = CechPic.pull (fst Z A).left (CechPic.pull x.left (cls L hL) - CechPic.pull x'.left (cls L hL))`. Rewrite using `[e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left]`.

Conclude with `sub_eq_sub_iff_sub_eq_sub.1 e₃`. Rewrite using `[cls_pull hD, e₂, ← pull_comp]`. Conclude with `pull_eq_zero_of_mem V (((fst Z A).left ⁻¹ᵁ V).ι ≫ (fst Z A).left) (fun z ↦ z.2) hc`.
-/
theorem memKL_mul_inv_of_eq (hL : L.IsLB) {Z : Over S} (x x' : Z ⟶ A)
    (h : ∀ (W : Over S) (a : W ⟶ A) (z : W ⟶ Z),
      CechPic.pull (a * (z ≫ x)).left (cls L hL) - CechPic.pull (z ≫ x).left (cls L hL) =
        CechPic.pull (a * (z ≫ x')).left (cls L hL) - CechPic.pull (z ≫ x').left (cls L hL)) :
    GlobalTheory.MemKL A L (x * x'⁻¹) := by
  intro p
  have hD : (Out.translDiff A L (x * x'⁻¹)).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero
    (CechPic.pull x.left (cls L hL) - CechPic.pull x'.left (cls L hL)) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  have e₁ := pull_translDiff hL (x * x'⁻¹) hD (fst Z A) (snd Z A)
  rw [lift_fst_snd, Over.id_left, pull_id] at e₁
  have k₁ : ((fst Z A ≫ x')⁻¹ * snd Z A) * (fst Z A ≫ x) = (fst Z A ≫ (x * x'⁻¹)) * snd Z A := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, mul_comm _ (fst Z A ≫ x)]
    exact (_root_.mul_assoc _ _ _).symm
  have k₂ : ((fst Z A ≫ x')⁻¹ * snd Z A) * (fst Z A ≫ x') = snd Z A := by
    rw [mul_comm, mul_inv_cancel_left]
  have e₃ := h (Z ⊗ A) ((fst Z A ≫ x')⁻¹ * snd Z A) (fst Z A)
  rw [k₁, k₂] at e₃
  have e₂ : cls _ hD = CechPic.pull (fst Z A).left
      (CechPic.pull x.left (cls L hL) - CechPic.pull x'.left (cls L hL)) := by
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left]
    exact sub_eq_sub_iff_sub_eq_sub.1 e₃
  rw [cls_pull hD, e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst Z A).left ⁻¹ᵁ V).ι ≫ (fst Z A).left) (fun z ↦ z.2) hc

end

/- English proof (translation)
Introduce `R _ _ A _ g hA _ L hL _ B P q hP _ hflat hsurj hev hKL`. Use `haveI : IsCommMonObj A := hA.comm`. Use `haveI : Flat q.left := hflat`. Use `haveI : Surjective q.left := hsurj`. Introduce `Y u u' hs`.

Rewrite `hs` using `[same_iff hP.isLB hP.isLB]`. Set `s₁` to `pullback.snd q.left u.left`. Set `f₁` to `pullback.fst q.left u.left`. Set `s₂` to `pullback.snd q.left (s₁ ≫ u'.left)`. Set `f₂` to `pullback.fst q.left (s₁ ≫ u'.left)`.

Set `Z : Over (Sp R)` to `Over.mk (s₂ ≫ s₁ ≫ Y.hom)`. Set `c : Z ⟶ Y` to `Over.homMk (s₂ ≫ s₁) (by simp [Z])`. Establish `w₁ : f₁ ≫ A.hom = s₁ ≫ Y.hom`. Rewrite using `[← Over.w q, pullback.condition_assoc, Over.w u]`. Establish `w₂ : f₂ ≫ A.hom = s₂ ≫ s₁ ≫ Y.hom`.

Rewrite using `[← Over.w q, pullback.condition_assoc, Category.assoc, Over.w u']`. Set `x : Z ⟶ A` to `Over.homMk (s₂ ≫ f₁) (by simp [Z, w₁])`. Set `x' : Z ⟶ A` to `Over.homMk f₂ (by simpa [Z] using w₂)`. Establish `hx : c ≫ u = x ≫ q` using `by ext1`. Simplify using `only [Over.comp_left, c, x, Over.homMk_left, Category.assoc]`.

Rewrite using `[pullback.condition]`. Establish `hx' : c ≫ u' = x' ≫ q` using `by ext1`. Simplify using `only [Over.comp_left, c, x', Over.homMk_left, Category.assoc]`. Rewrite using `[pullback.condition]`. Establish `hK : GlobalTheory.MemKL A L (x * x'⁻¹)`.

Use `memKL_mul_inv_of_eq hL x x' fun W a z ↦ ?_` and prove the remaining obligations. Establish `e` using `congrArg (CechPic.pull (lift a (z ≫ c)).left) hs`. Rewrite `e` using `[pull_evc, pull_evc, lift_fst, lift_snd_assoc, lift_snd_assoc]`. Simplify using `only [Category.assoc] at e`. Rewrite `e` using `[hx, hx', ← Category.assoc, ← Category.assoc, hev, hev]`.

Rewrite `e`, the goal using `[← sub_eq_zero]`. Use `e using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws. Establish `hq : x ≫ q = x' ≫ q` using `(hKL Z x x').2 hK`. Establish `: Epi c.left`.

Establish `: Flat c.left` using `by simp only [c, Over.homMk_left]; infer_instance`. Establish `: Surjective c.left` using `by simp only [c, Over.homMk_left]; infer_instance`. Conclude with `Flat.epi_of_flat_of_surjective _`. Establish `: Epi c` using `Over.epi_of_epi_left c`. Rewrite using `[← cancel_epi c, hx, hx', hq]`.
-/
theorem inj_of_quotient : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∀ (B : Over (Sp R)) (P : LB (A ⊗ B).left) (q : A ⟶ B) (hP : Fam A P), IsFinite q.left → Flat q.left → Surjective q.left → (∀ (Y : Over (Sp R)) (a x : Y ⟶ A), evc hP.isLB a (x ≫ q) = GlobalTheory.CechPic.pull (a * x).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) - GlobalTheory.CechPic.pull x.left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL)) → (∀ (Y : Over (Sp R)) (x y : Y ⟶ A), x ≫ q = y ≫ q ↔ GlobalTheory.MemKL A L (x * y⁻¹)) → Inj A P := by
  intro R _ _ A _ g hA _ L hL _ B P q hP _ hflat hsurj hev hKL
  haveI : IsCommMonObj A := hA.comm
  haveI : Flat q.left := hflat
  haveI : Surjective q.left := hsurj
  intro Y u u' hs
  rw [same_iff hP.isLB hP.isLB] at hs
  let s₁ := pullback.snd q.left u.left
  let f₁ := pullback.fst q.left u.left
  let s₂ := pullback.snd q.left (s₁ ≫ u'.left)
  let f₂ := pullback.fst q.left (s₁ ≫ u'.left)
  let Z : Over (Sp R) := Over.mk (s₂ ≫ s₁ ≫ Y.hom)
  let c : Z ⟶ Y := Over.homMk (s₂ ≫ s₁) (by simp [Z])
  have w₁ : f₁ ≫ A.hom = s₁ ≫ Y.hom := by
    rw [← Over.w q, pullback.condition_assoc, Over.w u]
  have w₂ : f₂ ≫ A.hom = s₂ ≫ s₁ ≫ Y.hom := by
    rw [← Over.w q, pullback.condition_assoc, Category.assoc, Over.w u']
  let x : Z ⟶ A := Over.homMk (s₂ ≫ f₁) (by simp [Z, w₁])
  let x' : Z ⟶ A := Over.homMk f₂ (by simpa [Z] using w₂)
  have hx : c ≫ u = x ≫ q := by
    ext1
    simp only [Over.comp_left, c, x, Over.homMk_left, Category.assoc]
    rw [pullback.condition]
  have hx' : c ≫ u' = x' ≫ q := by
    ext1
    simp only [Over.comp_left, c, x', Over.homMk_left, Category.assoc]
    rw [pullback.condition]
  have hK : GlobalTheory.MemKL A L (x * x'⁻¹) := by
    refine memKL_mul_inv_of_eq hL x x' fun W a z ↦ ?_
    have e := congrArg (CechPic.pull (lift a (z ≫ c)).left) hs
    rw [pull_evc, pull_evc, lift_fst, lift_snd_assoc, lift_snd_assoc] at e
    simp only [Category.assoc] at e
    rw [hx, hx', ← Category.assoc, ← Category.assoc, hev, hev] at e
    rw [← sub_eq_zero] at e ⊢
    convert e using 1
    abel
  have hq : x ≫ q = x' ≫ q := (hKL Z x x').2 hK
  have : Epi c.left := by
    have : Flat c.left := by simp only [c, Over.homMk_left]; infer_instance
    have : Surjective c.left := by simp only [c, Over.homMk_left]; infer_instance
    exact Flat.epi_of_flat_of_surjective _
  have : Epi c := Over.epi_of_epi_left c
  rw [← cancel_epi c, hx, hx', hq]

end GlobalTheory.DualCon

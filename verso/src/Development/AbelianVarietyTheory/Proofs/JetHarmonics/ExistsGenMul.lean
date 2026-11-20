import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.IsUnivChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.CubicNormMulIdentity

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaMul

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

/- English proof (translation)
Establish `e₁` using `UUA.hv_comp C k a B b x`. Establish `e₂` using `C.N_split k a B b`. Establish `e₃ : hv θ k a B b = cubN θ k a B b * (θ a b B)⁻¹` using `rfl`. Rewrite using `[mul_comm b B]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Establish `a₁` using `congrArg Additive.ofMul e₁`. Establish `a₂` using `congrArg Additive.ofMul e₂`. Establish `a₃` using `congrArg Additive.ofMul e₃`. Establish `b₁` using `congrArg Additive.ofMul h₁`. Establish `b₂` using `congrArg Additive.ofMul h₂`.

Simplify using `only [ofMul_mul, ofMul_inv] at a₁ a₂ a₃ b₁ b₂ ⊢`. Take the linear combination `(norm := abel) a₁ + a₂ + a₃ - b₁ + b₂`.
-/
theorem alg {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (C : IsCub θ) (k : ℕ) (a B b x : A)
    (g₁ g g₂ gs gy w w₁ : U) (h₁ : g₂ * θ a b B = g * g₁) (h₂ : gs * θ a (B ^ k) b = g * gy) :
    hv θ k a B (x * b) * (g₁ * w₁) * (hv θ k (a * B ^ k) b x * (gs * w)) =
      hv θ k a (b * B) x * (g₂ * (cubN θ k 1 B b * gy * (w * w₁))) := by
  have e₁ := UUA.hv_comp C k a B b x
  have e₂ := C.N_split k a B b
  have e₃ : hv θ k a B b = cubN θ k a B b * (θ a b B)⁻¹ := rfl
  rw [mul_comm b B]
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  have a₃ := congrArg Additive.ofMul e₃
  have b₁ := congrArg Additive.ofMul h₁
  have b₂ := congrArg Additive.ofMul h₂
  simp only [ofMul_mul, ofMul_inv] at a₁ a₂ a₃ b₁ b₂ ⊢
  linear_combination (norm := abel) a₁ + a₂ + a₃ - b₁ + b₂

/- English proof (translation)
Take `⟨N, hN, vN⟩` from `exists_cubN D.cub (1 : TF (R := R) F ⟶ D.P.A) p₁.g.b p.g.b k`. Take `⟨w₂, hw₂, v₂⟩` from `exists_gen D.P.isLB (φ' := DegPre.lineφ D F b₂) (ε' := DegPre.lineε k) (fun U _ h => by`. Establish `l : ∀ b : TF (R` using `R) F ⟶ D.P.A, ∏ i, h (DegPre.lineφ D F b i) ^ DegPre.lineε k i = h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h b.left ^ (-(k : ℤ)) := fun b => by`. Rewrite using `[Fin.prod_univ_two]`. Both sides reduce to the same expression.

Establish `g : ∏ i, h (DegPre.gtφ D F p.g.b p₁.y i) ^ DegPre.gtε i = h (p₁.g.b ^ k * p.g.b).left ^ (-1 : ℤ) * h (p₁.g.b ^ k).left ^ (1 : ℤ) * h p.g.b.left ^ (1 : ℤ) * h (1 : TF (R` using `R) F ⟶ D.P.A).left ^ (-1 : ℤ) := by`. Rewrite using `[Fin.prod_univ_four, ← cPoint_y p₁]`. Both sides reduce to the same expression. Use `Eq.trans (prod_sum₂ (K := Fin 8 ⊕ Fin 4) (K' := Fin 2 ⊕ Fin 2) (U := U) _ (prod_sum₂ (K := Fin 8) (K' := Fin 4) (U := U) _ rfl g) (prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _ (l _) (l _))) (Eq.trans ?_ (l b₂).symm)` and prove the remaining obligations. Rewrite using `[hb, mul_comm p.g.b p₁.g.b]`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `[Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]`. Use the proof step `module)`. Use the proof step `(LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (p.g.s p₁.y)) (LB.mulGen D.P.L _ _ _ _ w w₁))`. Use the proof step `(mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN (p.g.isGen _)) (mulGen_isGen _ _ _ _ _ _ _ hw hw₁))`.

Use `⟨w₂, hw₂, fun T σ z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[v₂ _ _ z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, vN T σ z J hJ, MonObj.comp_one]`.
-/
theorem exists_gen_mul {k : ℕ} (p p₁ : QkPt D F k) (b₂ : TF (R := R) F ⟶ D.P.A) (hb : b₂ = p.g.b * p₁.g.b)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)))
    (w₁ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p₁.g.b) (DegPre.lineε k))) (hw : w.IsGen) (hw₁ : w₁.IsGen) :
    ∃ w₂ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F b₂) (DegPre.lineε k)), w₂.IsGen ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (σ : T ⟶ TF (R := R) F) (z : T.left) (J), Good D.P.L z J →
        val w₂ σ.left z J = cubN (th D z J) k 1 (σ ≫ p₁.g.b) (σ ≫ p.g.b) * val (p.g.s p₁.y) σ.left z J *
          (val w σ.left z J * val w₁ σ.left z J) := by
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub (1 : TF (R := R) F ⟶ D.P.A) p₁.g.b p.g.b k
  obtain ⟨w₂, hw₂, v₂⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b₂) (ε' := DegPre.lineε k) (fun U _ h => by
      have l : ∀ b : TF (R := R) F ⟶ D.P.A, ∏ i, h (DegPre.lineφ D F b i) ^ DegPre.lineε k i =
          h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h b.left ^ (-(k : ℤ)) := fun b => by
        rw [Fin.prod_univ_two]; rfl
      have g : ∏ i, h (DegPre.gtφ D F p.g.b p₁.y i) ^ DegPre.gtε i =
          h (p₁.g.b ^ k * p.g.b).left ^ (-1 : ℤ) * h (p₁.g.b ^ k).left ^ (1 : ℤ) * h p.g.b.left ^ (1 : ℤ) *
            h (1 : TF (R := R) F ⟶ D.P.A).left ^ (-1 : ℤ) := by
        rw [Fin.prod_univ_four, ← cPoint_y p₁]; rfl
      refine Eq.trans (prod_sum₂ (K := Fin 8 ⊕ Fin 4) (K' := Fin 2 ⊕ Fin 2) (U := U) _
        (prod_sum₂ (K := Fin 8) (K' := Fin 4) (U := U) _ rfl g)
        (prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _ (l _) (l _))) (Eq.trans ?_ (l b₂).symm)
      rw [hb, mul_comm p.g.b p₁.g.b]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (p.g.s p₁.y)) (LB.mulGen D.P.L _ _ _ _ w w₁))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN (p.g.isGen _)) (mulGen_isGen _ _ _ _ _ _ _ hw hw₁))
  refine ⟨w₂, hw₂, fun T σ z J hJ => ?_⟩
  rw [v₂ _ _ z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, vN T σ z J hJ, MonObj.comp_one]

/- English proof (translation)
Establish `hb : p₂.g.b = p.g.b * p₁.g.b` using `hg.1`. Take `⟨w₂, hw₂, v₂⟩` from `exists_gen_mul p p₁ p₂.g.b hb w w₁ hw hw₁`. Use `⟨w₂, hw₂, fun s t t' h₁ h => ?_⟩` and prove the remaining obligations. Rewrite `h₁` using `[phiRel_iff hG _ _ hw₁]`. Rewrite `h` using `[phiRel_iff hG _ _ hw]`.

Rewrite using `[phiRel_iff hG _ _ hw₂]`. Introduce `α β hαβ T ρ z J hJ`. Establish `C : IsCub (th D z J)` using `isCub_cubV D.cub hJ`. Establish `e` using `h (α + p₁.y) β (by rw [← hαβ, hy]; abel) T ρ z J hJ`. Establish `e₁` using `h₁ α (α + p₁.y) rfl T (ρ ≫ DegPre.trPt D F p.g.b) z J hJ`.

Establish `hf : (ρ ≫ DegPre.trPt D F p.g.b) ≫ fst (TF (R` using `R) F) D.P.A = ρ ≫ fst _ _ := by`. Rewrite using `[Category.assoc, tr_fst]`. Establish `hp : (ρ ≫ DegPre.trPt D F p.g.b) ≫ DegPre.prB D F = (ρ ≫ DegPre.prB D F) * ((ρ ≫ fst _ _) ≫ p.g.b)`. Rewrite using `[Category.assoc, tr_pr, MonObj.comp_mul, ← Category.assoc]`. Establish `ht : (ρ ≫ DegPre.trPt D F p.g.b) ≫ DegPre.trPt D F p₁.g.b = ρ ≫ DegPre.trPt D F p₂.g.b`.

Rewrite using `[Category.assoc, trPt_mul, hb]`. Establish `hy₁ : cP D T p₁.y = ((ρ ≫ fst _ _) ≫ p₁.g.b) ^ k`. Rewrite using `[← comp_cP D (ρ ≫ fst (TF (R := R) F) D.P.A), cPoint_y]`. Conclude with `map_pow (preHom (ρ ≫ fst (TF (R := R) F) D.P.A)) _ _`. Establish `u₁ : uVal D F k α p₁.g.b (ρ ≫ DegPre.trPt D F p.g.b) z J = hv (th D z J) k (cP D T α) ((ρ ≫ fst _ _) ≫ p₁.g.b) ((ρ ≫ DegPre.prB D F) * ((ρ ≫ fst _ _) ≫ p.g.b))`.

Rewrite using `[uVal, hp, ← Category.assoc (ρ ≫ DegPre.trPt D F p.g.b), hf]`. Both sides reduce to the same expression. Establish `u₂ : uVal D F k (α + p₁.y) p.g.b ρ z J = hv (th D z J) k (cP D T α * ((ρ ≫ fst _ _) ≫ p₁.g.b) ^ k) ((ρ ≫ fst _ _) ≫ p.g.b) (ρ ≫ DegPre.prB D F)`. Rewrite using `[uVal, cPoint_add, hy₁, ← Category.assoc]`. Both sides reduce to the same expression.

Establish `u₃ : uVal D F k α p₂.g.b ρ z J = hv (th D z J) k (cP D T α) (((ρ ≫ fst _ _) ≫ p.g.b) * ((ρ ≫ fst _ _) ≫ p₁.g.b)) (ρ ≫ DegPre.prB D F)`. Rewrite using `[uVal, ← Category.assoc, hb, MonObj.comp_mul]`. Both sides reduce to the same expression. Establish `g₁ : val (p₂.g.s α) (ρ ≫ fst _ _).left z J * th D z J (cP D T α) ((ρ ≫ fst _ _) ≫ p.g.b) ((ρ ≫ fst _ _) ≫ p₁.g.b) = val (p.g.s α) (ρ ≫ fst _ _).left z J * val (p₁.g.s α) (ρ ≫ fst _ _).left z J`. Use `(val_mul hJ _ _ _).symm.trans ((val_corr hJ (hg.2 α) (ρ ≫ fst (TF (R := R) F) D.P.A).left).trans (val_mul hJ _ _ _))` as an intermediate fact.

Use `Eq.trans (congrArg₂ (· * ·) rfl ?_) this` and prove the remaining obligations. Use `Eq.trans ?_ (val_cub D.cub (ρ ≫ fst (TF (R := R) F) D.P.A) hJ (cP D _ α) p.g.b p₁.g.b).symm` and prove the remaining obligations. Rewrite using `[comp_cP]`. Establish `g₂` using `gt_mul (ρ ≫ fst (TF (R := R) F) D.P.A) hJ p.g α p₁.y`. Rewrite `g₂` using `[hy₁]`.

Rewrite `e₁` using `[ht, hf, u₁, val_mul hJ]`. Rewrite `e` using `[e₁, u₂, val_mul hJ, _root_.mul_assoc, ← Units.val_mul, alg C k _ _ _ _ _ _ _ _ _ _ _ g₁ g₂]`. Rewrite using `[e, u₃, val_mul hJ, v₂ T _ z J hJ]`.
-/
theorem phi_mul_core (hG : GlobalFnsSt) {k : ℕ} (p p₁ p₂ : QkPt D F k) (hy : p₂.y = p.y + p₁.y)
    (hg : p.g.IsAdd p₁.g p₂.g)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)))
    (w₁ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p₁.g.b) (DegPre.lineε k))) (hw : w.IsGen) (hw₁ : w₁.IsGen) :
    ∃ w₂ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p₂.g.b) (DegPre.lineε k)), w₂.IsGen ∧
      ∀ s t t' : Fam D F k, PhiRel D F k p₁ w₁ s t → PhiRel D F k p w t t' → PhiRel D F k p₂ w₂ s t' := by
  have hb : p₂.g.b = p.g.b * p₁.g.b := hg.1
  obtain ⟨w₂, hw₂, v₂⟩ := exists_gen_mul p p₁ p₂.g.b hb w w₁ hw hw₁
  refine ⟨w₂, hw₂, fun s t t' h₁ h => ?_⟩
  rw [phiRel_iff hG _ _ hw₁] at h₁
  rw [phiRel_iff hG _ _ hw] at h
  rw [phiRel_iff hG _ _ hw₂]
  intro α β hαβ T ρ z J hJ
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have e := h (α + p₁.y) β (by rw [← hαβ, hy]; abel) T ρ z J hJ
  have e₁ := h₁ α (α + p₁.y) rfl T (ρ ≫ DegPre.trPt D F p.g.b) z J hJ
  have hf : (ρ ≫ DegPre.trPt D F p.g.b) ≫ fst (TF (R := R) F) D.P.A = ρ ≫ fst _ _ := by
    rw [Category.assoc, tr_fst]
  have hp : (ρ ≫ DegPre.trPt D F p.g.b) ≫ DegPre.prB D F = (ρ ≫ DegPre.prB D F) * ((ρ ≫ fst _ _) ≫ p.g.b) := by
    rw [Category.assoc, tr_pr, MonObj.comp_mul, ← Category.assoc]
  have ht : (ρ ≫ DegPre.trPt D F p.g.b) ≫ DegPre.trPt D F p₁.g.b = ρ ≫ DegPre.trPt D F p₂.g.b := by
    rw [Category.assoc, trPt_mul, hb]
  have hy₁ : cP D T p₁.y = ((ρ ≫ fst _ _) ≫ p₁.g.b) ^ k := by
    rw [← comp_cP D (ρ ≫ fst (TF (R := R) F) D.P.A), cPoint_y]; exact map_pow (preHom (ρ ≫ fst (TF (R := R) F) D.P.A)) _ _
  have u₁ : uVal D F k α p₁.g.b (ρ ≫ DegPre.trPt D F p.g.b) z J =
      hv (th D z J) k (cP D T α) ((ρ ≫ fst _ _) ≫ p₁.g.b) ((ρ ≫ DegPre.prB D F) * ((ρ ≫ fst _ _) ≫ p.g.b)) := by
    rw [uVal, hp, ← Category.assoc (ρ ≫ DegPre.trPt D F p.g.b), hf]; rfl
  have u₂ : uVal D F k (α + p₁.y) p.g.b ρ z J =
      hv (th D z J) k (cP D T α * ((ρ ≫ fst _ _) ≫ p₁.g.b) ^ k) ((ρ ≫ fst _ _) ≫ p.g.b) (ρ ≫ DegPre.prB D F) := by
    rw [uVal, cPoint_add, hy₁, ← Category.assoc]; rfl
  have u₃ : uVal D F k α p₂.g.b ρ z J =
      hv (th D z J) k (cP D T α) (((ρ ≫ fst _ _) ≫ p.g.b) * ((ρ ≫ fst _ _) ≫ p₁.g.b)) (ρ ≫ DegPre.prB D F) := by
    rw [uVal, ← Category.assoc, hb, MonObj.comp_mul]; rfl
  have g₁ : val (p₂.g.s α) (ρ ≫ fst _ _).left z J *
      th D z J (cP D T α) ((ρ ≫ fst _ _) ≫ p.g.b) ((ρ ≫ fst _ _) ≫ p₁.g.b) =
      val (p.g.s α) (ρ ≫ fst _ _).left z J * val (p₁.g.s α) (ρ ≫ fst _ _).left z J := by
    have := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hg.2 α) (ρ ≫ fst (TF (R := R) F) D.P.A).left).trans
      (val_mul hJ _ _ _))
    refine Eq.trans (congrArg₂ (· * ·) rfl ?_) this
    refine Eq.trans ?_ (val_cub D.cub (ρ ≫ fst (TF (R := R) F) D.P.A) hJ (cP D _ α) p.g.b p₁.g.b).symm
    rw [comp_cP]
  have g₂ := gt_mul (ρ ≫ fst (TF (R := R) F) D.P.A) hJ p.g α p₁.y
  rw [hy₁] at g₂
  rw [ht, hf, u₁, val_mul hJ] at e₁
  rw [e₁, u₂, val_mul hJ, _root_.mul_assoc, ← Units.val_mul, alg C k _ _ _ _ _ _ _ _ _ _ _ g₁ g₂] at e
  rw [e, u₃, val_mul hJ, v₂ T _ z J hJ]

end GlobalTheory.ThetaMul

namespace GlobalTheory

/- English proof (translation)
Introduce `hL V _ _ _ D F _ _ k _ p p₁ p₂ hy hg w w₁ hw hw₁`. Conclude with `ThetaMul.phi_mul_core hL.globalFns p p₁ p₂ hy hg w w₁ hw hw₁`.
-/
theorem phi_mul : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ p p₁ p₂ : QkPt D.toPre F k, p₂.y = p.y + p₁.y → p.g.IsAdd p₁.g p₂.g → ∀ (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (w₁ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₁.g.b) (DegPre.lineε k))), w.IsGen → w₁.IsGen → ∃ w₂ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₂.g.b) (DegPre.lineε k)), w₂.IsGen ∧ ∀ s t t' : Fam D.toPre F k, PhiRel D.toPre F k p₁ w₁ s t → PhiRel D.toPre F k p w t t' → PhiRel D.toPre F k p₂ w₂ s t' := by
  intro hL V _ _ _ D F _ _ k _ p p₁ p₂ hy hg w w₁ hw hw₁
  exact ThetaMul.phi_mul_core hL.globalFns p p₁ p₂ hy hg w w₁ hw hw₁

end GlobalTheory

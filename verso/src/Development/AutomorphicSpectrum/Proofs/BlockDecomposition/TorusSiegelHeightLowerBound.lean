import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CvecSurjective

set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov.FirstLower

section Helpers

open PositivityTheory.ThKEst (rId)
open PositivityTheory.ThKEst.Sieg (rId_add rId_zero' rId_snd)
open GroundTheory.Automorphic.Anisotropic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rIdele [IsTotallyReal F] (c : ℝ) : GroundTheory.Global.IdeleGroup F where
  val := rId F c
  inv := rId F (-c)
  val_inv := by rw [← rId_add, add_neg_cancel, rId_zero']
  inv_val := by rw [← rId_add, neg_add_cancel, rId_zero']

/- English proof (translation)
Establish `hm : ∀ w : InfinitePlace F, w.mult = 1` using `fun w => by`. Rewrite using `[InfinitePlace.mult, if_pos (IsTotallyReal.isReal w)]`. Establish `hinf : ∀ w : InfinitePlace F, ‖(rId F c).1 w‖ ^ w.mult = Real.exp c` using `fun w => by`. Rewrite using `[hm, pow_one]`. Conclude with `norm_evInf_rId w c`.

Establish `hfin : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ‖(rId F c).2 v‖ = 1` using `fun v => by`. Rewrite using `[rId_snd]`. Conclude with `norm_one`. Establish `e : (GroundTheory.Global.IdeleGroup.ideleModule F (rIdele c) : ℝ) = (∏ w : InfinitePlace F, ‖(rId F c).1 w‖ ^ w.mult) * ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ‖(rId F c).2 v‖` using `GroundTheory.Global.IdeleGroup.ideleModule_eq _`. Rewrite using `[e, finprod_eq_one_of_forall_eq_one hfin, mul_one, Finset.prod_congr rfl fun w _ => hinf w, Finset.prod_const, Finset.card_univ, card_infinitePlace, ← Real.exp_nat_mul]`.
-/
theorem ideleModule_rIdele [IsTotallyReal F] (c : ℝ) :
    (GroundTheory.Global.IdeleGroup.ideleModule F (rIdele c) : ℝ) = Real.exp ((Module.finrank ℚ F : ℝ) * c) := by
  have hm : ∀ w : InfinitePlace F, w.mult = 1 := fun w => by
    rw [InfinitePlace.mult, if_pos (IsTotallyReal.isReal w)]
  have hinf : ∀ w : InfinitePlace F, ‖(rId F c).1 w‖ ^ w.mult = Real.exp c := fun w => by
    rw [hm, pow_one]
    exact norm_evInf_rId w c
  have hfin : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ‖(rId F c).2 v‖ = 1 := fun v => by
    rw [rId_snd]
    exact norm_one
  have e : (GroundTheory.Global.IdeleGroup.ideleModule F (rIdele c) : ℝ) =
      (∏ w : InfinitePlace F, ‖(rId F c).1 w‖ ^ w.mult) *
        ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ‖(rId F c).2 v‖ :=
    GroundTheory.Global.IdeleGroup.ideleModule_eq _
  rw [e, finprod_eq_one_of_forall_eq_one hfin, mul_one, Finset.prod_congr rfl fun w _ => hinf w,
    Finset.prod_const, Finset.card_univ, card_infinitePlace, ← Real.exp_nat_mul]

variable {n r : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `h1 : (M *ᵥ ratV F (Xᵀ 0)) i = (M * adMat F X) i 0` using `rfl`. Rewrite using `[h1, h, Matrix.mul_apply, Finset.sum_eq_single 0]`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Conclude with `mul_comm _ _`.

Introduce `j _ hj`. Rewrite using `[hB (show id (0 : Fin (r + 1)) < id j from Fin.pos_of_ne_zero hj), mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem mulVec_ratV_col {X : Matrix (Fin n) (Fin (r + 1)) E} {M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)}
    {B : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)} (hB : B.BlockTriangular id)
    (h : M * adMat F X = adMat F X * B) : M *ᵥ ratV F (Xᵀ 0) = B 0 0 • ratV F (Xᵀ 0) := by
  funext i
  have h1 : (M *ᵥ ratV F (Xᵀ 0)) i = (M * adMat F X) i 0 := rfl
  rw [h1, h, Matrix.mul_apply, Finset.sum_eq_single 0]
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_comm _ _
  · intro j _ hj
    rw [hB (show id (0 : Fin (r + 1)) < id j from Fin.pos_of_ne_zero hj), mul_zero]
  · simp

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[ratV, map_mul]`.
-/
theorem ratV_smul (e : E) (w : Fin n → E) : ratV F (e • w) = inclR (F := F) (AF F) e • ratV F w := by
  funext i
  simp [ratV, map_mul]

/- English proof (translation)
Establish `e : algebraMap (AF F) (AF F ⊗[F] E) c • ξ = c • ξ`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, ← Algebra.smul_def]`. Rewrite using `[e]`. Use `conv_lhs => rw [← ofResVec_resVec (Module.finBasis F E) (AF F) ξ, ← ofResVec_smul, resVec_ofResVec]`.
-/
theorem resVec_algebraMap_smul [Algebra.IsQuadraticExtension F E] (c : AF F) (ξ : Fin n → AF F ⊗[F] E) :
    resVec (ι := Fin n) (Module.finBasis F E) (AF F) (algebraMap (AF F) (AF F ⊗[F] E) c • ξ) =
      c • resVec (ι := Fin n) (Module.finBasis F E) (AF F) ξ := by
  have e : algebraMap (AF F) (AF F ⊗[F] E) c • ξ = c • ξ := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, ← Algebra.smul_def]
  rw [e]
  conv_lhs => rw [← ofResVec_resVec (Module.finBasis F E) (AF F) ξ, ← ofResVec_smul, resVec_ofResVec]

variable {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin (r + 1)) E}

/- English proof (translation)
Establish `h0 : a 0 = 1`. Use `ha.add 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `left_eq_mul.1 this`. Rewrite using `[inv_eq_iff_mul_eq_one, ← ha.add, add_neg_cancel, h0]`.
-/
theorem IsTorus.inv_eq {a : (Fin (r + 1) → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) (s : Fin (r + 1) → ℝ) :
    (a s)⁻¹ = a (-s) := by
  have h0 : a 0 = 1 := by
    have := ha.add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  rw [inv_eq_iff_mul_eq_one, ← ha.add, add_neg_cancel, h0]

/- English proof (translation)
Take `⟨B, hB, hpB⟩` from `hp`. Establish `h1` using `mulVec_ratV_col hB hpB`. Establish `h2` using `mulVec_ratV_col (Matrix.blockTriangular_diagonal _) (ha.onX (-s))`. Rewrite `h2` using `[Matrix.diagonal_apply_eq]`. Rewrite using `[IsTorus.inv_eq ha, ratV_smul, Matrix.mulVec_smul, h1, Matrix.mulVec_smul, Matrix.mulVec_smul, h2]`.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem torus_inv_mulVec {a : (Fin (r + 1) → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) {p : GAd σ J}
    (hp : p ∈ minPar σ J X) (s : Fin (r + 1) → ℝ) (e : E) :
    (matHom _ σ J (a s)⁻¹).1 *ᵥ ((matHom _ σ J p).1 *ᵥ ratV F (e • Xᵀ 0)) =
      algebraMap (AF F) (AF F ⊗[F] E) (rId F (-s 0)) • ((matHom _ σ J p).1 *ᵥ ratV F (e • Xᵀ 0)) := by
  obtain ⟨B, hB, hpB⟩ := hp
  have h1 := mulVec_ratV_col hB hpB
  have h2 := mulVec_ratV_col (Matrix.blockTriangular_diagonal _) (ha.onX (-s))
  rw [Matrix.diagonal_apply_eq] at h2
  rw [IsTorus.inv_eq ha, ratV_smul, Matrix.mulVec_smul, h1, Matrix.mulVec_smul, Matrix.mulVec_smul, h2]
  funext i
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Introduce `h0`. Establish `h1` using `congrFun (congrFun hW.xy 0) 0`. Establish `hc : ∀ i, X i 0 = 0` using `fun i => congrFun h0 i`. Simplify using `[cT, Matrix.mul_apply, hc] at h1`.
-/
theorem col_ne_zero (hW : IsWittFrame σ J X Y) : Xᵀ 0 ≠ 0 := by
  intro h0
  have h1 := congrFun (congrFun hW.xy 0) 0
  have hc : ∀ i, X i 0 = 0 := fun i => congrFun h0 i
  simp [cT, Matrix.mul_apply, hc] at h1

end Helpers

open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic GlobalTheory.CompanionTheory.RedCov.Bridge in

/- English proof (translation)
Establish `step : ∀ (g : GAd σ J) (ξ : Fin n → AF F ⊗[F] E), resVec (ι` using `Fin n) (Module.finBasis F E) (AF F) ξ ᵥ* (trG σ J g).1 = resVec (ι := Fin n) (Module.finBasis F E) (AF F) ((matHom _ σ J g⁻¹).1 *ᵥ ξ) := fun g ξ => by`. Rewrite using `[trG, MonoidHom.comp_apply, map_inv]`. Conclude with `resVec_vecMul_trHom _ _ _ _`. Rewrite using `[ratVec_cvec, step, step, torus_inv_mulVec ha hω, resVec_algebraMap_smul]`. Both sides reduce to the same expression.
-/
theorem vecMul_trG_torus {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {X Y : Matrix (Fin n) (Fin (r + 1)) E} {a : (Fin (r + 1) → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a)
    {ω : GAd σ J} (hω : ω⁻¹ ∈ minPar σ J X) (s : Fin (r + 1) → ℝ) (e : E) :
    (Reduction.ratVec (cvec F (e • Xᵀ 0)) ᵥ* (trG σ J ω).1) ᵥ* (trG σ J (a s)).1 =
      ((rIdele (-s 0) : GroundTheory.Global.IdeleGroup F) : AF F) •
        (Reduction.ratVec (cvec F (e • Xᵀ 0)) ᵥ* (trG σ J ω).1) := by
  have step : ∀ (g : GAd σ J) (ξ : Fin n → AF F ⊗[F] E),
      resVec (ι := Fin n) (Module.finBasis F E) (AF F) ξ ᵥ* (trG σ J g).1 =
        resVec (ι := Fin n) (Module.finBasis F E) (AF F) ((matHom _ σ J g⁻¹).1 *ᵥ ξ) := fun g ξ => by
    rw [trG, MonoidHom.comp_apply, map_inv]
    exact resVec_vecMul_trHom _ _ _ _
  rw [ratVec_cvec, step, step, torus_inv_mulVec ha hω, resVec_algebraMap_smul]
  rfl

open GroundTheory.Automorphic GlobalTheory.CompanionTheory.RedCov.Bridge in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h n J hJ r X Y hW a ha Ω C hΩ hΩP hC`. Use `haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩`. Use `haveI : IsTotallyReal F := h.1`. Establish `hcont : Continuous fun g : GAd σ J => (trG σ J g)⁻¹` using `(continuous_trG σ J).inv`. Take `⟨P₁, hP₁, hb₁⟩` from `Reduction.exists_adelicNorm_vecMul_le_mul (hC.image hcont)`.

Take `⟨P₂, hP₂, hb₂⟩` from `Reduction.exists_adelicNorm_vecMul_le_mul (hΩ.image hcont)`. Use `⟨P₁ * P₂, mul_pos hP₁ hP₂, fun ω hω s κ hκ e he => ?_⟩` and prove the remaining obligations. Establish `hv : e • Xᵀ 0 ≠ 0` using `smul_ne_zero he (col_ne_zero hW)`. Establish `hc0` using `cvec_ne_zero (F := F) hv`. Use `set y₀ := Reduction.ratVec (cvec F (e • Xᵀ 0)) with hy₀`.

Establish `hf₀ : Reduction.HasFiniteContent y₀` using `Reduction.hasFiniteContent_ratVec hc0`. Use `set y₁ := y₀ ᵥ* (trG σ J ω).1 with hy₁`. Establish `hf₁ : Reduction.HasFiniteContent y₁` using `hf₀.vecMul (trG σ J ω)`. Use `set u := rIdele (F := F) (-s 0) with hu`. Establish `hkey : y₁ ᵥ* (trG σ J (a s)).1 = (u : AF F) • y₁` using `vecMul_trG_torus ha (inv_mem_minPar h hJ hW (hΩP hω)) s e`.

Establish `hg : hgt σ J (ω * a s * κ) (e • Xᵀ 0) = Reduction.adelicNorm (((u : AF F) • y₁) ᵥ* (trG σ J κ).1)`. Rewrite using `[hgt_eq, Reduction.height, map_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, ← hy₀, ← hy₁, hkey]`. Establish `hf₂ : Reduction.HasFiniteContent (((u : AF F) • y₁) ᵥ* (trG σ J κ).1)` using `(hf₁.smul u).vecMul (trG σ J κ)`. Establish `hb3 : Reduction.adelicNorm ((u : AF F) • y₁) ≤ P₁ * hgt σ J (ω * a s * κ) (e • Xᵀ 0)`. Use `hb₁ _ ⟨κ, hκ, rfl⟩ _ hf₂` as an intermediate fact.

Rewrite `this` using `[Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one, ← hg]`. Then use the resulting hypothesis. Establish `hb4 : Reduction.adelicNorm y₀ ≤ P₂ * Reduction.adelicNorm y₁`. Use `hb₂ _ ⟨ω, hω, rfl⟩ _ hf₁` as an intermediate fact. Rewrite `this` using `[hy₁, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]`. Then use the resulting hypothesis. Establish `h1 : 1 ≤ Reduction.adelicNorm y₀` using `Reduction.one_le_adelicNorm_ratVec hc0`.

Establish `hsm : Reduction.adelicNorm ((u : AF F) • y₁) = Real.exp (- ((Module.finrank ℚ F : ℝ) * s 0)) * Reduction.adelicNorm y₁`. Rewrite using `[Reduction.adelicNorm_smul hf₁ u, hu, ideleModule_rIdele, mul_neg]`. Establish `hexp` using `Real.exp_pos (- ((Module.finrank ℚ F : ℝ) * s 0))`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exp_le_hgt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ a, IsTorus σ J X Y a → ∀ (Ω C : Set (GAd σ J)), IsCompact Ω → Ω ⊆ minPar σ J X → IsCompact C → ∃ P : ℝ, 0 < P ∧ ∀ ω ∈ Ω, ∀ s : Fin (r + 1) → ℝ, ∀ κ ∈ C, ∀ e : E, e ≠ 0 → Real.exp (- ((Module.finrank ℚ F : ℝ) * s 0)) ≤ P * hgt σ J (ω * a s * κ) (e • Xᵀ 0) := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW a ha Ω C hΩ hΩP hC
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  haveI : IsTotallyReal F := h.1
  have hcont : Continuous fun g : GAd σ J => (trG σ J g)⁻¹ := (continuous_trG σ J).inv
  obtain ⟨P₁, hP₁, hb₁⟩ := Reduction.exists_adelicNorm_vecMul_le_mul (hC.image hcont)
  obtain ⟨P₂, hP₂, hb₂⟩ := Reduction.exists_adelicNorm_vecMul_le_mul (hΩ.image hcont)
  refine ⟨P₁ * P₂, mul_pos hP₁ hP₂, fun ω hω s κ hκ e he => ?_⟩
  have hv : e • Xᵀ 0 ≠ 0 := smul_ne_zero he (col_ne_zero hW)
  have hc0 := cvec_ne_zero (F := F) hv
  set y₀ := Reduction.ratVec (cvec F (e • Xᵀ 0)) with hy₀
  have hf₀ : Reduction.HasFiniteContent y₀ := Reduction.hasFiniteContent_ratVec hc0
  set y₁ := y₀ ᵥ* (trG σ J ω).1 with hy₁
  have hf₁ : Reduction.HasFiniteContent y₁ := hf₀.vecMul (trG σ J ω)
  set u := rIdele (F := F) (-s 0) with hu
  have hkey : y₁ ᵥ* (trG σ J (a s)).1 = (u : AF F) • y₁ :=
    vecMul_trG_torus ha (inv_mem_minPar h hJ hW (hΩP hω)) s e
  have hg : hgt σ J (ω * a s * κ) (e • Xᵀ 0) = Reduction.adelicNorm (((u : AF F) • y₁) ᵥ* (trG σ J κ).1) := by
    rw [hgt_eq, Reduction.height, map_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.vecMul_vecMul,
      ← Matrix.vecMul_vecMul, ← hy₀, ← hy₁, hkey]
  have hf₂ : Reduction.HasFiniteContent (((u : AF F) • y₁) ᵥ* (trG σ J κ).1) := (hf₁.smul u).vecMul (trG σ J κ)
  have hb3 : Reduction.adelicNorm ((u : AF F) • y₁) ≤ P₁ * hgt σ J (ω * a s * κ) (e • Xᵀ 0) := by
    have := hb₁ _ ⟨κ, hκ, rfl⟩ _ hf₂
    rwa [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one, ← hg] at this
  have hb4 : Reduction.adelicNorm y₀ ≤ P₂ * Reduction.adelicNorm y₁ := by
    have := hb₂ _ ⟨ω, hω, rfl⟩ _ hf₁
    rwa [hy₁, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one] at this
  have h1 : 1 ≤ Reduction.adelicNorm y₀ := Reduction.one_le_adelicNorm_ratVec hc0
  have hsm : Reduction.adelicNorm ((u : AF F) • y₁) =
      Real.exp (- ((Module.finrank ℚ F : ℝ) * s 0)) * Reduction.adelicNorm y₁ := by
    rw [Reduction.adelicNorm_smul hf₁ u, hu, ideleModule_rIdele, mul_neg]
  have hexp := Real.exp_pos (- ((Module.finrank ℚ F : ℝ) * s 0))
  calc Real.exp (- ((Module.finrank ℚ F : ℝ) * s 0))
      ≤ Real.exp (- ((Module.finrank ℚ F : ℝ) * s 0)) * (P₂ * Reduction.adelicNorm y₁) :=
        le_mul_of_one_le_right hexp.le (h1.trans hb4)
    _ = P₂ * Reduction.adelicNorm ((u : AF F) • y₁) := by rw [hsm]; ring
    _ ≤ P₂ * (P₁ * hgt σ J (ω * a s * κ) (e • Xᵀ 0)) := mul_le_mul_of_nonneg_left hb3 hP₂.le
    _ = P₁ * P₂ * hgt σ J (ω * a s * κ) (e • Xᵀ 0) := by ring

end GlobalTheory.CompanionTheory.RedCov.FirstLower

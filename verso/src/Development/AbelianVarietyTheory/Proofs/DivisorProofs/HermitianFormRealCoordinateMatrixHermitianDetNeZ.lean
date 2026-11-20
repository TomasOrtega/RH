import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

namespace GlobalTheory.RealWeilF

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [conjTranspose_apply, map_apply]`. Rewrite using `[← hcm, hJ]`.
-/
theorem map_conjTranspose_of_herm {n : ℕ} (σ : E →ₐ[F] E) (hcm : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x))
    {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = J i j) (τ : E →+* ℂ) : (J.map τ)ᴴ = J.map τ := by
  ext i j
  simp only [conjTranspose_apply, map_apply]
  rw [← hcm, hJ]

/- English proof (translation)
Introduce `him`. Establish `h1 : star (τ ξ₀) = -τ ξ₀` using `by rw [← hcm, hσ, map_neg]`. Establish `hre : (τ ξ₀).re = 0`. Use `congrArg Complex.re h1` as an intermediate fact. Simplify using `only [Complex.star_def, Complex.conj_re, Complex.neg_re] at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `: τ ξ₀ = 0` using `Complex.ext hre him`. Conclude with `h0 ((map_eq_zero τ).1 this)`.
-/
theorem im_ne_zero_of_skew (σ : E →ₐ[F] E) (hcm : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x))
    {ξ₀ : E} (h0 : ξ₀ ≠ 0) (hσ : σ ξ₀ = -ξ₀) (τ : E →+* ℂ) : (τ ξ₀).im ≠ 0 := by
  intro him
  have h1 : star (τ ξ₀) = -τ ξ₀ := by rw [← hcm, hσ, map_neg]
  have hre : (τ ξ₀).re = 0 := by
    have := congrArg Complex.re h1
    simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at this
    linarith
  have : τ ξ₀ = 0 := Complex.ext hre him
  exact h0 ((map_eq_zero τ).1 this)

/- English proof (translation)
Establish `hdS : ∀ w, IsUnit (JS.map (tau w)).det` using `fun w => by`. Establish `e` using `RingHom.map_det (tau w) JS`. Rewrite `e` using `[RingHom.mapMatrix_apply]`. Rewrite using `[← e]`. Conclude with `(isUnit_iff_ne_zero.2 ((map_ne_zero (tau w)).2 hS.2))`.

Establish `hdT : ∀ w, IsUnit (JT.map (tau w)).det` using `fun w => by`. Establish `e` using `RingHom.map_det (tau w) JT`. Rewrite `e` using `[RingHom.mapMatrix_apply]`. Rewrite using `[← e]`. Conclude with `(isUnit_iff_ne_zero.2 ((map_ne_zero (tau w)).2 hT.2))`.

Establish `hc : ∀ w, ((2 * (tau w ξ₀).im : ℝ) : ℂ) ≠ 0` using `fun w => by`. Use `im_ne_zero_of_skew σ hcm h0 hσ (tau w)` as an intermediate fact. Conclude with `mul_ne_zero two_ne_zero this` after adjusting the coercions. Prove the components needed by the constructor for the conclusion. Unfold `HMF`.

Rewrite using `[GlobalTheory.RealWeil.blk_conjTranspose]`. Apply the tactic sequence `congr 1 <;> funext w`. Rewrite using `[conjTranspose_smul, map_conjTranspose_of_herm σ hcm hT.1]`. Simplify using the standard rewrite rules. Rewrite using `[conjTranspose_nonsing_inv, map_conjTranspose_of_herm σ hcm hS.1]`.

Establish `: HMF JS JT ξ₀ tau * GlobalTheory.RealWeil.blk (fun w => ((2 * (tau w ξ₀).im : ℝ) : ℂ)⁻¹ • (JT.map (tau w))⁻¹) (fun w => JS.map (tau w)) = 1`. Unfold `HMF`. Rewrite using `[GlobalTheory.RealWeil.blk_mul, ← GlobalTheory.RealWeil.blk_one]`. Apply the tactic sequence `congr 1 <;> funext w`. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ (hc w), one_smul, mul_nonsing_inv _ (hdT w)]`.

Rewrite using `[mul_nonsing_inv _ (hdS w)]`. Conclude with `(isUnit_det_of_right_inverse this).ne_zero`.
-/
theorem hermitianFormRealCoordinateBlock_hermitian_det {nS nT : ℕ} (σ : E →ₐ[F] E) (hcm : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x))
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (hS : IsHermND σ JS) (hT : IsHermND σ JT) (ξ₀ : E) (h0 : ξ₀ ≠ 0) (hσ : σ ξ₀ = -ξ₀)
    (tau : InfinitePlace F → (E →+* ℂ)) :
    (HMF JS JT ξ₀ tau)ᴴ = HMF JS JT ξ₀ tau ∧ (HMF JS JT ξ₀ tau).det ≠ 0 := by
  classical
  have hdS : ∀ w, IsUnit (JS.map (tau w)).det := fun w => by
    have e := RingHom.map_det (tau w) JS
    rw [RingHom.mapMatrix_apply] at e
    rw [← e]; exact (isUnit_iff_ne_zero.2 ((map_ne_zero (tau w)).2 hS.2))
  have hdT : ∀ w, IsUnit (JT.map (tau w)).det := fun w => by
    have e := RingHom.map_det (tau w) JT
    rw [RingHom.mapMatrix_apply] at e
    rw [← e]; exact (isUnit_iff_ne_zero.2 ((map_ne_zero (tau w)).2 hT.2))
  have hc : ∀ w, ((2 * (tau w ξ₀).im : ℝ) : ℂ) ≠ 0 := fun w => by
    have := im_ne_zero_of_skew σ hcm h0 hσ (tau w)
    exact_mod_cast mul_ne_zero two_ne_zero this
  constructor
  · unfold HMF
    rw [GlobalTheory.RealWeil.blk_conjTranspose]
    congr 1 <;> funext w
    · rw [conjTranspose_smul, map_conjTranspose_of_herm σ hcm hT.1]
      simp
    · rw [conjTranspose_nonsing_inv, map_conjTranspose_of_herm σ hcm hS.1]
  · have : HMF JS JT ξ₀ tau * GlobalTheory.RealWeil.blk (fun w => ((2 * (tau w ξ₀).im : ℝ) : ℂ)⁻¹ • (JT.map (tau w))⁻¹)
        (fun w => JS.map (tau w)) = 1 := by
      unfold HMF
      rw [GlobalTheory.RealWeil.blk_mul, ← GlobalTheory.RealWeil.blk_one]
      congr 1 <;> funext w
      · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ (hc w), one_smul,
          mul_nonsing_inv _ (hdT w)]
      · rw [mul_nonsing_inv _ (hdS w)]
    exact (isUnit_det_of_right_inverse this).ne_zero

end GlobalTheory.RealWeilF

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hσ`. Conclude with `GlobalTheory.RealWeilF.hermitianFormRealCoordinateBlock_hermitian_det σ hB.cm.2.2.2 JS JT hS hT ξ₀ h0 hσ _`.
-/
theorem GlobalTheory.RealWeilF.HMF_herm_det : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1))ᴴ = HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) ∧ (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1)).det ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hσ
  exact GlobalTheory.RealWeilF.hermitianFormRealCoordinateBlock_hermitian_det σ hB.cm.2.2.2 JS JT hS hT ξ₀ h0 hσ _

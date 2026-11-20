import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsTheta
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

noncomputable section

namespace KThetaSummandNorm

/- English proof (translation)
Simplify using `only [dotProduct, mulVec, periodMatrix, Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_sum, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.I_re, Complex.I_im]`. Simplify using the standard rewrite rules.
-/
lemma im_dot_period {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (w v : Fin g → ℝ) :
    ((fun i => (w i : ℂ)) ⬝ᵥ (periodMatrix X Y *ᵥ fun i => (v i : ℂ))).im = w ⬝ᵥ (Y *ᵥ v) := by
  simp only [dotProduct, mulVec, periodMatrix, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_sum, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply,
    smul_eq_mul, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.I_re, Complex.I_im]
  simp

/- English proof (translation)
Simplify using `[dotProduct, Complex.im_sum]`.
-/
lemma im_dot_real {g : ℕ} (w c : Fin g → ℝ) :
    ((fun i => (w i : ℂ)) ⬝ᵥ fun i => (c i : ℂ)).im = 0 := by
  simp [dotProduct, Complex.im_sum]

/- English proof (translation)
Establish `h : u ⬝ᵥ (Y *ᵥ w) = w ⬝ᵥ (Y *ᵥ u)`. Rewrite using `[dotProduct_mulVec, ← vecMul_transpose, hY.eq, dotProduct_comm]`. Simplify using `only [qf, mulVec_add, dotProduct_add, add_dotProduct, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma qf_add {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.IsSymm) (w u : Fin g → ℝ) :
    qf Y (w + u) = qf Y w + 2 * (w ⬝ᵥ (Y *ᵥ u)) + qf Y u := by
  have h : u ⬝ᵥ (Y *ᵥ w) = w ⬝ᵥ (Y *ᵥ u) := by
    rw [dotProduct_mulVec, ← vecMul_transpose, hY.eq, dotProduct_comm]
  simp only [qf, mulVec_add, dotProduct_add, add_dotProduct, h]
  ring

end KThetaSummandNorm

open KThetaSummandNorm in
/- English proof (translation)
Introduce `g X Y a b u₁ u₂ k hY`. Use `set w : Fin g → ℝ := intVec k + a with hw`. Establish `hW : (fun i => ((intVec k i + a i : ℝ) : ℂ)) = fun i => (w i : ℂ)` using `rfl`. Establish `hzb : (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ)) + (fun i => (b i : ℂ)) = periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => ((u₂ + b) i : ℂ)`. Use extensionality with `i`.

Simplify using `[add_assoc]`. Establish `hre : (π * Complex.I * ((fun i => (w i : ℂ)) ⬝ᵥ (periodMatrix X Y *ᵥ fun i => (w i : ℂ))) + 2 * π * Complex.I * ((fun i => (w i : ℂ)) ⬝ᵥ (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => ((u₂ + b) i : ℂ)))).re = -π * qf Y w - 2 * π * (w ⬝ᵥ (Y *ᵥ u₁))`. Rewrite using `[dotProduct_add]`. Simplify using `only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.add_im, im_dot_period, im_dot_real]`. Simplify using `only [qf]`.

Expand and normalize the polynomial expressions, which then agree. Unfold `thetaSummand`. Rewrite using `[hW, hzb, Complex.norm_exp, hre, ← Real.exp_add]`. Use `congr 1`. Establish `: intVec k + a + u₁ = w + u₁` using `rfl`.

Rewrite using `[this, qf_add Y hY w u₁]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ThetaSummandNorm.proof : ThetaSummandNorm.Statement := by
  intro g X Y a b u₁ u₂ k hY
  set w : Fin g → ℝ := intVec k + a with hw
  have hW : (fun i => ((intVec k i + a i : ℝ) : ℂ)) = fun i => (w i : ℂ) := rfl
  have hzb : (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ)) +
      (fun i => (b i : ℂ)) =
      periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => ((u₂ + b) i : ℂ) := by
    ext i; simp [add_assoc]
  have hre : (π * Complex.I *
      ((fun i => (w i : ℂ)) ⬝ᵥ (periodMatrix X Y *ᵥ fun i => (w i : ℂ))) +
      2 * π * Complex.I * ((fun i => (w i : ℂ)) ⬝ᵥ
        (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => ((u₂ + b) i : ℂ)))).re =
      -π * qf Y w - 2 * π * (w ⬝ᵥ (Y *ᵥ u₁)) := by
    rw [dotProduct_add]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.add_im,
      im_dot_period, im_dot_real]
    simp only [qf]
    ring
  unfold thetaSummand
  rw [hW, hzb, Complex.norm_exp, hre, ← Real.exp_add]
  congr 1
  have : intVec k + a + u₁ = w + u₁ := rfl
  rw [this, qf_add Y hY w u₁]
  ring

end

end GroundTheory.Heights₂.Heights

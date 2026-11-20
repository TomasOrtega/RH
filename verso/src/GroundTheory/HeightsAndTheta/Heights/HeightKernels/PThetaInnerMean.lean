import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsTheta
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ThetaGauss
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real MeasureTheory

noncomputable section

namespace KThetaInnerMean

/- English proof (translation)
Unfold `thetaSummand torusChar`. Rewrite using `[← Complex.exp_add, ← Complex.exp_add]`. Use `congr 1`. Simplify using `only [dotProduct, Pi.add_apply, Pi.zero_apply, intVec, Complex.ofReal_zero, add_zero, mul_add, add_mul, Finset.sum_add_distrib, Complex.ofReal_add, Complex.ofReal_intCast, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_ofNat]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thetaSummand_shift {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b u₁ u₂ : Fin g → ℝ)
    (k : Fin g → ℤ) :
    thetaSummand X Y a b (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ)) k =
      Complex.exp (((2 * π * ∑ i, a i * u₂ i : ℝ) : ℂ) * Complex.I) *
        (thetaSummand X Y a b
            (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => ((0 : Fin g → ℝ) i : ℂ)) k *
          torusChar k u₂) := by
  unfold thetaSummand torusChar
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [dotProduct, Pi.add_apply, Pi.zero_apply, intVec, Complex.ofReal_zero, add_zero,
    mul_add, add_mul, Finset.sum_add_distrib, Complex.ofReal_add, Complex.ofReal_intCast,
    Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_ofNat]
  ring

end KThetaInnerMean

open KThetaInnerMean in

/- English proof (translation)
Introduce `g X Y a b u₁ hY`. Establish `hS : Y.IsSymm`. Establish `h` using `hY.isHermitian`. Rewrite `h` using `[Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]`. Conclude with `h`.

Use `set E : ℝ := exp (-π * qf Y u₁) with hE`. Establish `hEpos : 0 < E` using `exp_pos _`. Use `set c : (Fin g → ℤ) → ℂ := fun k => thetaSummand X Y a b (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => ((0 : Fin g → ℝ) i : ℂ)) k with hc`. Establish `hcE : ∀ k, ‖c k‖ * E = exp (-π * qf Y (intVec k + a + u₁))` using `fun k => h₁ g X Y a b u₁ 0 k hS`. Establish `hcs : Summable fun k => ‖c k‖`.

Establish `hs` using `(KTheta.summable_exp_qf Y hY π pi_pos (a + u₁)).mul_right E⁻¹`. Use `hs.congr fun k => ?_` and prove the remaining obligations. Rewrite using `[← add_assoc, ← hcE k, mul_assoc, mul_inv_cancel₀ hEpos.ne', mul_one]`. Establish `hN : ∀ u₂, thetaNorm X Y a b u₁ u₂ ^ 2 = ‖∑' k, c k * torusChar k u₂‖ ^ 2 * E ^ 2`. Introduce `u₂`.

Establish `h : thetaNorm X Y a b u₁ u₂ = ‖∑' k, thetaSummand X Y a b (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ)) k‖ * E` using `rfl`. Rewrite using `[h, tsum_congr (fun k => thetaSummand_shift X Y a b u₁ u₂ k), tsum_mul_left, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]`. Conclude with `mul_pow _ _ _`. Simplify using `only [hN]`. Rewrite using `[integral_mul_const, h₂ g c hcs, ← tsum_mul_right]`.

Use `tsum_congr fun k => ?_` and prove the remaining obligations. Rewrite using `[← mul_pow, hcE k, ← exp_nat_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ThetaInnerMean.proof (h₁ : ThetaSummandNorm.Statement) (h₂ : ThetaCubeParseval.Statement) :
    ThetaInnerMean.Statement := by
  intro g X Y a b u₁ hY
  have hS : Y.IsSymm := by
    have h := hY.isHermitian
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  set E : ℝ := exp (-π * qf Y u₁) with hE
  have hEpos : 0 < E := exp_pos _
  set c : (Fin g → ℤ) → ℂ := fun k => thetaSummand X Y a b
    (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => ((0 : Fin g → ℝ) i : ℂ)) k with hc
  have hcE : ∀ k, ‖c k‖ * E = exp (-π * qf Y (intVec k + a + u₁)) := fun k =>
    h₁ g X Y a b u₁ 0 k hS
  have hcs : Summable fun k => ‖c k‖ := by
    have hs := (KTheta.summable_exp_qf Y hY π pi_pos (a + u₁)).mul_right E⁻¹
    refine hs.congr fun k => ?_
    rw [← add_assoc, ← hcE k, mul_assoc, mul_inv_cancel₀ hEpos.ne', mul_one]
  have hN : ∀ u₂, thetaNorm X Y a b u₁ u₂ ^ 2 = ‖∑' k, c k * torusChar k u₂‖ ^ 2 * E ^ 2 := by
    intro u₂
    have h : thetaNorm X Y a b u₁ u₂ = ‖∑' k, thetaSummand X Y a b
        (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ)) k‖ * E := rfl
    rw [h, tsum_congr (fun k => thetaSummand_shift X Y a b u₁ u₂ k), tsum_mul_left, norm_mul,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    exact mul_pow _ _ _
  simp only [hN]
  rw [integral_mul_const, h₂ g c hcs, ← tsum_mul_right]
  refine tsum_congr fun k => ?_
  rw [← mul_pow, hcE k, ← exp_nat_mul]
  congr 1
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights

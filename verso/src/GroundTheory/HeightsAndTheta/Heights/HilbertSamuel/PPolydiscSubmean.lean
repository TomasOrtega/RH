import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergman
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PolydiscMean
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Metric Real

noncomputable section

/- English proof (translation)
Establish `hn' : (n : ℝ) ≠ 0` using `by exact_mod_cast hn.ne'`. Establish `hρ : 0 < R / Real.sqrt n` using `div_pos hR (Real.sqrt_pos.mpr (by exact_mod_cast hn))`. Establish `hsq : (R / Real.sqrt n) ^ 2 = R ^ 2 / n`. Rewrite using `[div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]`. Establish `hball : closedBall (0 : Fin D → ℂ) (R / Real.sqrt n) = Set.univ.pi fun _ => closedBall (0 : ℂ) (R / Real.sqrt n)`.

Rewrite using `[closedBall_pi _ hρ.le]`. Both sides reduce to the same expression. Establish `hw : ∀ z : Fin D → ℂ, Real.exp (-(n : ℝ) * ∑ j, lam j * ‖z j‖ ^ 2) = ∏ j, Real.exp (-((n : ℝ) * lam j) * ‖z j‖ ^ 2)`. Introduce `z`. Rewrite using `[← Real.exp_sum, Finset.mul_sum]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hfac : ∀ j, ∫ x in closedBall (0 : ℂ) (R / Real.sqrt n), Real.exp (-((n : ℝ) * lam j) * ‖x‖ ^ 2) = gaussDiscMass (lam j) R * (n : ℝ)⁻¹`. Introduce `j`.

Rewrite using `[integral_closedBall_gauss _ _ hρ.le, gaussDiscMass]`. Distinguish the cases in `hl : lam j = 0`. Rewrite using `[if_pos (by simp [hl]), if_pos hl, hsq]`. Expand and normalize the polynomial expressions, which then agree. Establish `hnl : (n : ℝ) * lam j ≠ 0` using `mul_ne_zero hn' hl`.

Rewrite using `[if_neg hnl, if_neg hl, hsq]`. Establish `e : -((n : ℝ) * lam j) * (R ^ 2 / n) = -lam j * R ^ 2`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Clear the denominators using the available nonvanishing facts.

Repeatedly rewrite using `[hw]`. Rewrite using `[hball, volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod (fun (j : Fin D) (x : ℂ) => Real.exp (-((n : ℝ) * lam j) * ‖x‖ ^ 2))]`. Repeatedly rewrite using `[hfac]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow, mul_comm]`.
-/
theorem integral_polydisc_gauss (D n : ℕ) (lam : Fin D → ℝ) (R : ℝ) (hn : 0 < n) (hR : 0 < R) :
    ∫ z in closedBall (0 : Fin D → ℂ) (R / Real.sqrt n),
        Real.exp (-(n : ℝ) * ∑ j, lam j * ‖z j‖ ^ 2) =
      ((n : ℝ) ^ D)⁻¹ * ∏ j, gaussDiscMass (lam j) R := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hρ : 0 < R / Real.sqrt n := div_pos hR (Real.sqrt_pos.mpr (by exact_mod_cast hn))
  have hsq : (R / Real.sqrt n) ^ 2 = R ^ 2 / n := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hball : closedBall (0 : Fin D → ℂ) (R / Real.sqrt n) =
      Set.univ.pi fun _ => closedBall (0 : ℂ) (R / Real.sqrt n) := by
    rw [closedBall_pi _ hρ.le]
    rfl
  have hw : ∀ z : Fin D → ℂ, Real.exp (-(n : ℝ) * ∑ j, lam j * ‖z j‖ ^ 2) =
      ∏ j, Real.exp (-((n : ℝ) * lam j) * ‖z j‖ ^ 2) := by
    intro z
    rw [← Real.exp_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hfac : ∀ j, ∫ x in closedBall (0 : ℂ) (R / Real.sqrt n),
      Real.exp (-((n : ℝ) * lam j) * ‖x‖ ^ 2) = gaussDiscMass (lam j) R * (n : ℝ)⁻¹ := by
    intro j
    rw [integral_closedBall_gauss _ _ hρ.le, gaussDiscMass]
    by_cases hl : lam j = 0
    · rw [if_pos (by simp [hl]), if_pos hl, hsq]
      ring
    · have hnl : (n : ℝ) * lam j ≠ 0 := mul_ne_zero hn' hl
      rw [if_neg hnl, if_neg hl, hsq]
      have e : -((n : ℝ) * lam j) * (R ^ 2 / n) = -lam j * R ^ 2 := by
        field_simp
      rw [e]
      field_simp
  simp_rw [hw]
  rw [hball, volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod
    (fun (j : Fin D) (x : ℂ) => Real.exp (-((n : ℝ) * lam j) * ‖x‖ ^ 2))]
  simp_rw [hfac]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow,
    mul_comm]

/- English proof (translation)
Introduce `D n lam R f hn hR _ hf`. Use `set w : (Fin D → ℂ) → ℝ := fun z => Real.exp (-(n : ℝ) * ∑ j, lam j * ‖z j‖ ^ 2) with hwdef`. Establish `hwc : Continuous w`. Rewrite using `[hwdef]`. Use `fun_prop`.

Establish `hw0 : ∀ z, 0 ≤ w z` using `fun z => (Real.exp_pos _).le`. Establish `hrot : ∀ (u : Circle) z, w ((u : ℂ) • z) = w z`. Introduce `u z`. Simplify using `only [hwdef, Pi.smul_apply, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]`. Establish `h` using `sq_norm_mul_setIntegral_le hf hwc hw0 hrot`.

Simplify using `only [hwdef] at h`. Rewrite `h` using `[integral_polydisc_gauss D n lam R hn hR, ← mul_assoc]`. Conclude with `h`.
-/
theorem PolydiscSubmean.proof : PolydiscSubmean.Statement := by
  intro D n lam R f hn hR _ hf
  set w : (Fin D → ℂ) → ℝ := fun z => Real.exp (-(n : ℝ) * ∑ j, lam j * ‖z j‖ ^ 2) with hwdef
  have hwc : Continuous w := by
    rw [hwdef]
    fun_prop
  have hw0 : ∀ z, 0 ≤ w z := fun z => (Real.exp_pos _).le
  have hrot : ∀ (u : Circle) z, w ((u : ℂ) • z) = w z := by
    intro u z
    simp only [hwdef, Pi.smul_apply, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
  have h := sq_norm_mul_setIntegral_le hf hwc hw0 hrot
  simp only [hwdef] at h
  rw [integral_polydisc_gauss D n lam R hn hR, ← mul_assoc] at h
  exact h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

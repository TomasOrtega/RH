import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LGrowth

open Complex Finset

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (authored)
The only positive moduli below three are one and two. Their unit groups are trivial, so every character agrees with the principal character on units, and both vanish on nonunits. A nonprincipal character therefore has modulus at least three.
-/
lemma three_le_modulus_of_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : 3 ≤ q := by
  by_contra h
  push_neg at h
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  interval_cases q
  all_goals
    apply hχ
    ext a
    have ha : a = 1 := by revert a; decide
    rw [ha]
    simp

/- English proof (authored)
Since q ≥ 3, the argument 3q is at least nine. The bound e < 3 gives exp(2) < 9, so monotonicity of the logarithm gives the result.
-/
lemma two_le_log_three_mul (q : ℕ) (hq : 3 ≤ q) : 2 ≤ Real.log (3 * q) := by
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; try norm_num
  rw [Real.le_log_iff_exp_le (by positivity), e2]
  nlinarith

/- English proof (authored)
Express the power as the exponential of t log x. The logarithm is nonnegative and at most log(3q). Bounding t by the given quotient and cancelling the positive logarithm makes the exponent at most three halves.
-/
private lemma rpow_le_exp_three_halves_of_le_log (q : ℕ) (hq : 3 ≤ q) (x t : ℝ) (hx : 1 ≤ x) (hxq : x ≤ 3 * q)
    (ht : t ≤ 3 / (2 * Real.log (3 * q))) : x ^ t ≤ Real.exp (3 / 2) := by
  have hL : 2 ≤ Real.log (3 * q) := two_le_log_three_mul q hq
  have hLpos : 0 < Real.log (3 * q) := by linarith
  have hx0 : 0 < x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlxL : Real.log x ≤ Real.log (3 * q) := Real.log_le_log hx0 hxq
  rw [Real.rpow_def_of_pos hx0]
  apply Real.exp_le_exp.2
  have h1 : Real.log x * t ≤ Real.log x * (3 / (2 * Real.log (3 * q))) := mul_le_mul_of_nonneg_left ht hlx
  have h2 : Real.log x * (3 / (2 * Real.log (3 * q))) ≤ Real.log (3 * q) * (3 / (2 * Real.log (3 * q))) :=
    mul_le_mul_of_nonneg_right hlxL (by positivity)
  have h3 : Real.log (3 * q) * (3 / (2 * Real.log (3 * q))) = 3 / 2 := by field_simp; try ring
  linarith

/- English proof (authored)
The condition x ≤ q implies x ≤ 3q. Apply the preceding power estimate with exponent equal to the permitted upper endpoint.
-/
lemma rpow_le_exp_near_one (q : ℕ) (hq : 3 ≤ q) (x : ℝ) (hx : 1 ≤ x) (hxq : x ≤ q) :
    x ^ (3 / (2 * Real.log (3 * q))) ≤ Real.exp (3 / 2) := by
  have hqR : (0 : ℝ) ≤ q := by positivity
  exact rpow_le_exp_three_halves_of_le_log q hq x _ hx (by linarith) le_rfl

/- English proof (authored)
Write the power with exponent −r as the power with exponent 1 − r divided by x. The lower bound on r makes 1 − r satisfy the preceding exponent bound. Multiply by the positive reciprocal of x.
-/
lemma rpow_neg_le_exp_inv_near_one (q : ℕ) (hq : 3 ≤ q) (x : ℝ) (hx : 1 ≤ x) (hxq : x ≤ q) (r : ℝ)
    (hr : 1 - 3 / (2 * Real.log (3 * q)) ≤ r) :
    x ^ (-r) ≤ Real.exp (3 / 2) * x⁻¹ := by
  have hx0 : 0 < x := by linarith
  have hqR : (0 : ℝ) ≤ q := by positivity
  have e : x ^ (-r) = x ^ (1 - r) * x⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hx0]
    congr 1
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (rpow_le_exp_three_halves_of_le_log q hq x (1 - r) hx (by linarith) (by linarith))
    (inv_nonneg.2 hx0.le)

/- English proof (authored)
Use the triangle inequality and the bound of one on every character value. The power estimate bounds each term by exp(3/2) divided by its index. Sum to q and use the harmonic sum bound of 1 + log q, which is at most 1 + log(3q).
-/
lemma partial_sum_norm_le_near_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q) (w : ℂ)
    (hw : 1 - 3 / (2 * Real.log (3 * q)) ≤ w.re) :
    ‖∑ n ∈ Icc 1 q, χ (n : ZMod q) * (n : ℂ) ^ (-w)‖ ≤ Real.exp (3 / 2) * (1 + Real.log (3 * q)) := by
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ n ∈ Icc 1 q, ‖χ (n : ZMod q) * (n : ℂ) ^ (-w)‖ ≤ Real.exp (3 / 2) * (n : ℝ)⁻¹ := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    have hχn : ‖χ (n : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hr := rpow_neg_le_exp_inv_near_one q hq n (by exact_mod_cast h1) (by exact_mod_cast h2) w.re hw
    calc ‖χ (n : ZMod q)‖ * (n : ℝ) ^ (-w.re) ≤ 1 * (Real.exp (3 / 2) * (n : ℝ)⁻¹) :=
          mul_le_mul hχn hr (by positivity) zero_le_one
      _ = _ := one_mul _
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hH : ∑ n ∈ Icc 1 q, ((n : ℝ))⁻¹ = (harmonic q : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  rw [hH]
  refine (harmonic_le_one_add_log q).trans ?_
  have : Real.log q ≤ Real.log (3 * q) := Real.log_le_log (by positivity) (by linarith)
  linarith

/- English proof (authored)
Use the partial-summation representation and split it at the modulus q. The finite character sum with power weights satisfies the preceding harmonic bound. The endpoint correction is at most exp(3/2), since the partial sums have norm at most q + 1 and the exponent estimate applies up to q + 1. The tail has the same scale multiplied by the ratio of the norm to the real part of the argument, at most eight. Add the three bounds and use log(3q) ≥ 2 to obtain the stated constant.
-/
lemma lfunction_norm_le_near_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (w : ℂ)
    (hw : 1 - 3 / (2 * Real.log (3 * q)) ≤ w.re) (hw4 : 1 / 4 ≤ w.re) (hw2 : ‖w‖ ≤ 2) :
    ‖DirichletCharacter.LFunction χ w‖ ≤ 38 * Real.exp (3 / 2) * Real.log (3 * q) := by
  have hq := three_le_modulus_of_ne_one χ hχ
  have hL := two_le_log_three_mul q hq
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hre0 : 0 < w.re := by linarith
  have hB : ∀ M, ‖Formalism.FX.LFunctionPartialSum.Ap χ M‖ ≤ (q : ℝ) + 1 := fun M => norm_character_sum_Icc_le χ hχ M
  have hpos : (0 : ℝ) < (q : ℝ) + 1 := by linarith
  have hx1 : (1 : ℝ) ≤ (q : ℝ) + 1 := by linarith
  have hx3 : (q : ℝ) + 1 ≤ 3 * q := by linarith
  have hpow : ((q : ℝ) + 1) * ((q : ℝ) + 1) ^ (-w.re) ≤ Real.exp (3 / 2) := by
    have := rpow_le_exp_three_halves_of_le_log q hq ((q : ℝ) + 1) (1 - w.re) hx1 hx3 (by linarith)
    rwa [sub_eq_add_neg, Real.rpow_add hpos, Real.rpow_one] at this
  rw [Formalism.FX.LFunctionPartialSum.LFunction_eq_G (χ := χ) hχ hB hre0]
  unfold Formalism.FX.LFunctionPartialSum.G
  rw [← Summable.sum_add_tsum_nat_add (q + 1) (Formalism.FX.LFunctionPartialSum.summable_dterm (χ := χ) hB hre0),
    eq_sub_of_add_eq (Formalism.FX.LFunctionPartialSum.partial_identity (χ := χ) w q)]
  have h1 := partial_sum_norm_le_near_one χ hq w hw
  have h2 : ‖Formalism.FX.LFunctionPartialSum.Ap χ q * ((q : ℂ) + 1) ^ (-w)‖ ≤ Real.exp (3 / 2) := by
    rw [norm_mul]
    have e : ((q : ℂ) + 1) = ((q + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    push_cast
    calc ‖Formalism.FX.LFunctionPartialSum.Ap χ q‖ * ((q : ℝ) + 1) ^ (-w.re) ≤ ((q : ℝ) + 1) * ((q : ℝ) + 1) ^ (-w.re) :=
          mul_le_mul_of_nonneg_right (hB q) (by positivity)
      _ ≤ _ := hpow
  have h3 : ‖∑' i, Formalism.FX.LFunctionPartialSum.dterm χ w (i + (q + 1))‖ ≤ 8 * Real.exp (3 / 2) := by
    refine (Formalism.FX.LFunctionPartialSum.norm_tail_le χ hB hre0 q).trans ?_
    have hw' : ‖w‖ / w.re ≤ 8 := by rw [div_le_iff₀ hre0]; linarith
    calc ((q : ℝ) + 1) * (‖w‖ / w.re) * ((q : ℝ) + 1) ^ (-w.re)
        = (‖w‖ / w.re) * (((q : ℝ) + 1) * ((q : ℝ) + 1) ^ (-w.re)) := by ring
      _ ≤ 8 * Real.exp (3 / 2) := mul_le_mul hw' hpow (by positivity) (by norm_num)
  have hsub := norm_sub_le (∑ n ∈ Icc 1 q, χ (n : ZMod q) * (n : ℂ) ^ (-w)) (Formalism.FX.LFunctionPartialSum.Ap χ q * ((q : ℂ) + 1) ^ (-w))
  refine (norm_add_le _ _).trans ?_
  have he := Real.exp_pos (3 / 2)
  have hk := mul_le_mul_of_nonneg_left (show 10 + Real.log (3 * q) ≤ 38 * Real.log (3 * q) by linarith) he.le
  nlinarith

/- English proof (authored)
Around the real point σ take the circle of radius 1/(2 log(3q)). The modulus lower bound makes this radius at most one quarter. The real parts on the circle stay within the range of the near-one estimate and at least one quarter, while the norms are at most two. Apply the Cauchy derivative estimate for the entire nonprincipal L-function. Dividing the circle bound by the radius gives the stated constant times the square of log(3q).
-/
theorem lfunction_deriv_near_one : LDerivNearOne := by
  refine ⟨76 * Real.exp (3 / 2), fun q _ χ hχ σ hσ1 hσ2 => ?_⟩
  have hq := three_le_modulus_of_ne_one χ hχ
  have hL := two_le_log_three_mul q hq
  have hLpos : 0 < Real.log (3 * q) := by linarith
  have hρ : 0 < 1 / (2 * Real.log (3 * q)) := by positivity
  have hd : DiffContOnCl ℂ (DirichletCharacter.LFunction χ) (Metric.ball (σ : ℂ) (1 / (2 * Real.log (3 * q)))) :=
    (DirichletCharacter.differentiable_LFunction hχ).diffContOnCl
  have hC : ∀ z ∈ Metric.sphere (σ : ℂ) (1 / (2 * Real.log (3 * q))),
      ‖DirichletCharacter.LFunction χ z‖ ≤ 38 * Real.exp (3 / 2) * Real.log (3 * q) := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hre : |(z - σ).re| ≤ 1 / (2 * Real.log (3 * q)) := by rw [← hz]; exact Complex.abs_re_le_norm _
    rw [Complex.sub_re, Complex.ofReal_re] at hre
    have h1 : 1 / Real.log (3 * q) ≤ 1 / 2 := by rw [div_le_iff₀ hLpos]; linarith
    have h2 : 1 / (2 * Real.log (3 * q)) ≤ 1 / 4 := by rw [div_le_iff₀ (by positivity)]; linarith
    have e3 : 3 / (2 * Real.log (3 * q)) = 1 / Real.log (3 * q) + 1 / (2 * Real.log (3 * q)) := by
      field_simp
      try ring
    have hab := abs_le.1 hre
    apply lfunction_norm_le_near_one χ hχ z
    · rw [e3]; linarith
    · linarith
    · calc ‖z‖ = ‖(z - σ) + σ‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - σ‖ + ‖(σ : ℂ)‖ := norm_add_le _ _
        _ ≤ 1 / 4 + 1 := by
          rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
          linarith
        _ ≤ 2 := by norm_num
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hd hC
  calc _ ≤ 38 * Real.exp (3 / 2) * Real.log (3 * q) / (1 / (2 * Real.log (3 * q))) := this
    _ = 76 * Real.exp (3 / 2) * Real.log (3 * q) ^ 2 := by field_simp; try ring

end Formalism.ZeroFreeDirichlet

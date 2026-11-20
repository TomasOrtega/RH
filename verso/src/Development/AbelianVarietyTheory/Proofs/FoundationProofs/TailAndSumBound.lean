import Mathlib
import Formalism.GL3MeanSquares.SmoothedRemainderRealIntegralFormula
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerReal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gl2L2IntegralityStatement

open Finset Filter Topology

namespace GlobalTheory.GoodCharacterTail

open Formalism.HermitianLattices.GL2PrimeSums

/- English proof (translation)
Take `⟨I, hI, hG⟩` from `GlobalTheory.TailIntegralOfSummatory.tail_integral a S hS Z hZ`. Establish `hZ0 : (0 : ℝ) < Z` using `by linarith`. Establish `hZc : (Z : ℂ) ≠ 0` using `by exact_mod_cast hZ0.ne'`. Establish `h1 : Gchi a S Z = Z * (∑ n ∈ Icc 1 ⌊Z⌋₊, a n / (n : ℂ)) - psum a Z - Z * S`. Unfold `Gchi psum`.

Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : S - ∑ n ∈ Icc 1 ⌊Z⌋₊, a n / (n : ℂ) = I - psum a Z / Z`. Rewrite `hG` using `[h1]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `-hG`. Establish `h3 : ‖I‖ ≤ B - ‖psum a Z‖ / Z`.

Use `le_of_tendsto hI.norm ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop Z] with U hU`. Establish `h4` using `intervalIntegral.norm_integral_le_integral_norm (f := fun u : ℝ => psum a u / (u : ℂ) ^ 2) (μ := MeasureTheory.volume) hU`. Establish `h5 : (fun u : ℝ => ‖psum a u / (u : ℂ) ^ 2‖) = fun u : ℝ => ‖psum a u‖ / u ^ 2`. Use function extensionality and compare the values at `u`.

Rewrite using `[norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]`. Rewrite `h4` using `[h5]`. Use `hB U hU` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[h2]`.

Establish `h6` using `norm_sub_le I (psum a Z / Z)`. Rewrite `h6` using `[norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ0]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem tail_le (a : ℕ → ℂ) (S : ℂ)
    (hS : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n / (n : ℂ)) atTop (𝓝 S))
    (Z B : ℝ) (hZ : 1 ≤ Z)
    (hB : ∀ U : ℝ, Z ≤ U → ‖psum a Z‖ / Z + (∫ u in Z..U, ‖psum a u‖ / u ^ 2) ≤ B) :
    ‖S - ∑ n ∈ Icc 1 ⌊Z⌋₊, a n / (n : ℂ)‖ ≤ B := by
  obtain ⟨I, hI, hG⟩ := GlobalTheory.TailIntegralOfSummatory.tail_integral a S hS Z hZ
  have hZ0 : (0 : ℝ) < Z := by linarith
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ0.ne'
  have h1 : Gchi a S Z = Z * (∑ n ∈ Icc 1 ⌊Z⌋₊, a n / (n : ℂ)) - psum a Z - Z * S := by
    unfold Gchi psum
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    ring
  have h2 : S - ∑ n ∈ Icc 1 ⌊Z⌋₊, a n / (n : ℂ) = I - psum a Z / Z := by
    rw [h1] at hG
    field_simp
    linear_combination -hG
  have h3 : ‖I‖ ≤ B - ‖psum a Z‖ / Z := by
    refine le_of_tendsto hI.norm ?_
    filter_upwards [eventually_ge_atTop Z] with U hU
    have h4 := intervalIntegral.norm_integral_le_integral_norm
      (f := fun u : ℝ => psum a u / (u : ℂ) ^ 2) (μ := MeasureTheory.volume) hU
    have h5 : (fun u : ℝ => ‖psum a u / (u : ℂ) ^ 2‖) = fun u : ℝ => ‖psum a u‖ / u ^ 2 := by
      funext u
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [h5] at h4
    have := hB U hU
    linarith
  rw [h2]
  have h6 := norm_sub_le I (psum a Z / Z)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ0] at h6
  linarith

/- English proof (translation)
Establish `h` using `(isLittleO_log_rpow_atTop hδ).bound hk`. Use `filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with x hx hx0`. Rewrite `hx` using `[Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 _)]`. Conclude with `(le_abs_self _).trans hx`.
-/
theorem eventually_log_le (k δ : ℝ) (hk : 0 < k) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, Real.log x ≤ k * x ^ δ := by
  have h := (isLittleO_log_rpow_atTop hδ).bound hk
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 _)] at hx
  exact (le_abs_self _).trans hx

/- English proof (translation)
Introduce `ε hε hε1 C₁ c₁ CM hC₁ hc₁ hCM`. Take `⟨C, c, hC, hc, hZ⟩` from `GlobalTheory.T.gl2a2_integral_bound_of_sums C₁ c₁ hC₁ hc₁`. Establish `e1` using `eventually_log_le (1 / 400) (ε / 4) (by norm_num) (by linarith)`. Establish `e2` using `eventually_log_le c (ε / 6) hc (by linarith)`. Establish `e3` using `(tendsto_rpow_atTop (show 0 < ε / 2 by linarith)).eventually_ge_atTop (5 * C)`.

Establish `e4` using `(tendsto_rpow_atTop (show 0 < ε / 6 by linarith)).eventually_ge_atTop 2`. Establish `e5` using `Real.tendsto_log_atTop.eventually_ge_atTop 1`. Establish `e6` using `eventually_ge_atTop (2 : ℝ)`. Take `⟨x₀, hx₀⟩` from `eventually_atTop.1 (e1.and (e2.and (e3.and (e4.and (e5.and e6)))))`. Use `⟨x₀, 400 + CM + 1, ?_⟩` and prove the remaining obligations.

Introduce `x hx Q hQ hQ1 hQ2 a S hS hM H1 H2`. Take `⟨f1, f2, f3, f4, f5, f6⟩` from `hx₀ x hx`. Establish `hx0 : 0 < x` using `by linarith`. Establish `hx1 : 1 ≤ x` using `by linarith`. Establish `hQ3 : 3 ≤ Q`.

Establish `h` using `Real.add_one_le_exp (Real.log Q)`. Rewrite `h` using `[Real.exp_log hQ]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hz2 : 2 ≤ x ^ (400 : ℝ)`. Establish `: x ^ (1 : ℝ) ≤ x ^ (400 : ℝ)` using `Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)`.

Rewrite `this` using `[Real.rpow_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlz : Real.log (x ^ (400 : ℝ)) = 400 * Real.log x` using `Real.log_rpow hx0 _`. Establish `ht` using `tail_le a S hS (x ^ (400 : ℝ)) _ (by linarith) (fun U hU => hZ Q a hQ3 H1 H2 _ U hz2 hU)`. Establish `hp : (x ^ (400 : ℝ)) ^ (-(1 : ℝ) / 400) = x⁻¹`.

Rewrite using `[← Real.rpow_mul hx0.le, ← Real.rpow_neg_one]`. Evaluate the numerical expressions. Establish `hl : Real.log (x ^ (400 : ℝ) * Q) = 400 * Real.log x + Real.log Q`. Rewrite using `[Real.log_mul (by positivity) hQ.ne', hlz]`. Rewrite `ht` using `[hp, hl]`.

Establish `hsq : x ^ (ε / 4) * x ^ (ε / 4) = x ^ (ε / 2)`. Rewrite using `[← Real.rpow_add hx0]`. Put the polynomial expressions in normal form. Establish `hsq2 : x ^ (ε / 2) * x ^ (ε / 2) = x ^ ε`. Rewrite using `[← Real.rpow_add hx0]`.

Put the polynomial expressions in normal form. Establish `hL : (400 * Real.log x + Real.log Q) ^ 2 ≤ 4 * x ^ (ε / 2)`. Establish `a1 : 0 ≤ 400 * Real.log x + Real.log Q` using `by linarith`. Establish `a2 : 400 * Real.log x + Real.log Q ≤ 2 * x ^ (ε / 4)` using `by linarith`. Use `pow_le_pow_left₀ a1 a2 2` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish `hQc : x * Q ^ (-c) ≤ 1`. Rewrite using `[Real.rpow_def_of_pos hQ]`. Use `nth_rewrite 1 [← Real.exp_log hx0]`. Rewrite using `[← Real.exp_add, Real.exp_le_one_iff]`.

Use `mul_le_mul_of_nonneg_left hQ1 hc.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1e : 1 ≤ x ^ (ε / 2)` using `Real.one_le_rpow hx1 (by linarith)`. Establish `key : x * ‖S - ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ)‖ ≤ x ^ ε`. Establish `b1` using `mul_le_mul_of_nonneg_left ht hx0.le`.

Establish `b2 : x * (C * (x⁻¹ * (400 * Real.log x + Real.log Q) ^ 2 + Q ^ (-c))) = C * ((400 * Real.log x + Real.log Q) ^ 2 + x * Q ^ (-c))`. Clear the denominators using the available nonvanishing facts. Rewrite `b1` using `[b2]`. Establish `b3 : C * ((400 * Real.log x + Real.log Q) ^ 2 + x * Q ^ (-c)) ≤ C * (5 * x ^ (ε / 2))` using `mul_le_mul_of_nonneg_left (by linarith) hC.le`. Establish `b4 : 5 * C * x ^ (ε / 2) ≤ x ^ (ε / 2) * x ^ (ε / 2)` using `mul_le_mul_of_nonneg_right f3 (by linarith)`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]`. Conclude with `key`. Establish `c1 : x ^ ε ≤ x`.

Establish `: x ^ ε ≤ x ^ (1 : ℝ)` using `Real.rpow_le_rpow_of_exponent_le hx1 hε1.le`. Rewrite `this` using `[Real.rpow_one]`. Then use the resulting hypothesis. Establish `c2 : ‖S - ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ)‖ ≤ 1`. Establish `: x * ‖S - ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ)‖ ≤ x * 1` using `by linarith`. Conclude with `le_of_mul_le_mul_left this hx0`.

Establish `c3 : ‖∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ)‖ ≤ 400 * Real.log x + CM`. Rewrite using `[← hlz]`. Use `le_trans ((norm_sum_le _ _).trans (le_of_eq ?_)) (hM _ (by linarith))` and prove the remaining obligations. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[norm_div, Complex.norm_natCast]`.

Establish `c4` using `norm_add_le (S - ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ)) (∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ))`. Rewrite `c4` using `[sub_add_cancel]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem tail_and_sum_bound : Formalism.HermitianLattices.GL2PrimeSums.TailSumBound := by
  intro ε hε hε1 C₁ c₁ CM hC₁ hc₁ hCM
  obtain ⟨C, c, hC, hc, hZ⟩ := GlobalTheory.T.gl2a2_integral_bound_of_sums C₁ c₁ hC₁ hc₁
  have e1 := eventually_log_le (1 / 400) (ε / 4) (by norm_num) (by linarith)
  have e2 := eventually_log_le c (ε / 6) hc (by linarith)
  have e3 := (tendsto_rpow_atTop (show 0 < ε / 2 by linarith)).eventually_ge_atTop (5 * C)
  have e4 := (tendsto_rpow_atTop (show 0 < ε / 6 by linarith)).eventually_ge_atTop 2
  have e5 := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have e6 := eventually_ge_atTop (2 : ℝ)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (e1.and (e2.and (e3.and (e4.and (e5.and e6)))))
  refine ⟨x₀, 400 + CM + 1, ?_⟩
  intro x hx Q hQ hQ1 hQ2 a S hS hM H1 H2
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hQ3 : 3 ≤ Q := by
    have h := Real.add_one_le_exp (Real.log Q)
    rw [Real.exp_log hQ] at h
    linarith
  have hz2 : 2 ≤ x ^ (400 : ℝ) := by
    have : x ^ (1 : ℝ) ≤ x ^ (400 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    rw [Real.rpow_one] at this
    linarith
  have hlz : Real.log (x ^ (400 : ℝ)) = 400 * Real.log x := Real.log_rpow hx0 _
  have ht := tail_le a S hS (x ^ (400 : ℝ)) _ (by linarith)
    (fun U hU => hZ Q a hQ3 H1 H2 _ U hz2 hU)
  have hp : (x ^ (400 : ℝ)) ^ (-(1 : ℝ) / 400) = x⁻¹ := by
    rw [← Real.rpow_mul hx0.le, ← Real.rpow_neg_one]
    norm_num
  have hl : Real.log (x ^ (400 : ℝ) * Q) = 400 * Real.log x + Real.log Q := by
    rw [Real.log_mul (by positivity) hQ.ne', hlz]
  rw [hp, hl] at ht
  have hsq : x ^ (ε / 4) * x ^ (ε / 4) = x ^ (ε / 2) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hsq2 : x ^ (ε / 2) * x ^ (ε / 2) = x ^ ε := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hL : (400 * Real.log x + Real.log Q) ^ 2 ≤ 4 * x ^ (ε / 2) := by
    have a1 : 0 ≤ 400 * Real.log x + Real.log Q := by linarith
    have a2 : 400 * Real.log x + Real.log Q ≤ 2 * x ^ (ε / 4) := by linarith
    have := pow_le_pow_left₀ a1 a2 2
    nlinarith
  have hQc : x * Q ^ (-c) ≤ 1 := by
    rw [Real.rpow_def_of_pos hQ]
    nth_rewrite 1 [← Real.exp_log hx0]
    rw [← Real.exp_add, Real.exp_le_one_iff]
    have := mul_le_mul_of_nonneg_left hQ1 hc.le
    linarith
  have h1e : 1 ≤ x ^ (ε / 2) := Real.one_le_rpow hx1 (by linarith)
  have key : x * ‖S - ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ)‖ ≤ x ^ ε := by
    have b1 := mul_le_mul_of_nonneg_left ht hx0.le
    have b2 : x * (C * (x⁻¹ * (400 * Real.log x + Real.log Q) ^ 2 + Q ^ (-c))) =
        C * ((400 * Real.log x + Real.log Q) ^ 2 + x * Q ^ (-c)) := by
      field_simp
    rw [b2] at b1
    have b3 : C * ((400 * Real.log x + Real.log Q) ^ 2 + x * Q ^ (-c)) ≤ C * (5 * x ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC.le
    have b4 : 5 * C * x ^ (ε / 2) ≤ x ^ (ε / 2) * x ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right f3 (by linarith)
    linarith
  refine ⟨?_, ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    exact key
  · have c1 : x ^ ε ≤ x := by
      have : x ^ ε ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hε1.le
      rwa [Real.rpow_one] at this
    have c2 : ‖S - ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ)‖ ≤ 1 := by
      have : x * ‖S - ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ)‖ ≤ x * 1 := by linarith
      exact le_of_mul_le_mul_left this hx0
    have c3 : ‖∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ)‖ ≤ 400 * Real.log x + CM := by
      rw [← hlz]
      refine le_trans ((norm_sum_le _ _).trans (le_of_eq ?_)) (hM _ (by linarith))
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [norm_div, Complex.norm_natCast]
    have c4 := norm_add_le (S - ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ))
      (∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ))
    rw [sub_add_cancel] at c4
    nlinarith

end GlobalTheory.GoodCharacterTail

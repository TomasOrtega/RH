import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar

open Finset UpperTheory.V.Bern

/- English proof (translation)
Rewrite using `[bernoulliFun, Polynomial.eval_map_algebraMap, ← eq_ratCast (algebraMap ℚ ℝ) x, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, eq_ratCast]`.
-/
private theorem polybound_cast (k : ℕ) (x : ℚ) :
    (((Polynomial.bernoulli k).eval x : ℚ) : ℝ) = bernoulliFun k (x : ℝ) := by
  rw [bernoulliFun, Polynomial.eval_map_algebraMap, ← eq_ratCast (algebraMap ℚ ℝ) x,
    Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, eq_ratCast]

/- English proof (translation)
Rewrite using `[fourier_apply]`. Conclude with `Circle.norm_coe _`.
-/
private theorem polybound_norm_fourier (n : ℤ) (y : UnitAddCircle) : ‖fourier n y‖ = 1 := by
  rw [fourier_apply]; exact Circle.norm_coe _

/- English proof (translation)
Establish `hs` using `hasSum_one_div_nat_pow_mul_fourier hk hx`. Establish `h2 : ∀ (m : ℤ) (y : UnitAddCircle), ‖fourier m y + (-1) ^ k * fourier (-m) y‖ ≤ 2`. Introduce `m y`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, polybound_norm_fourier, polybound_norm_fourier]`.

Evaluate the numerical expressions. Establish `hbound : ‖-(2 * (Real.pi : ℂ) * Complex.I) ^ k / (k.factorial : ℂ) * (bernoulliFun k x : ℂ)‖ ≤ 2 * (Real.pi ^ 2 / 6)`. Rewrite using `[← hs.tsum_eq]`. Use `tsum_of_norm_bounded (hasSum_zeta_two.mul_left 2) fun n ↦ ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Establish `h1 : ‖1 / (n : ℂ) ^ k‖ ≤ 1 / (n : ℝ) ^ 2`. Rewrite using `[norm_div, norm_one, norm_pow, Complex.norm_natCast]`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using `[zero_pow (by omega : k ≠ 0)]`. Establish `hn1 : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`.

Conclude with `one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hn1 hk)`. Combine the equalities or inequalities in the displayed calculation. Establish `hnorm : ‖-(2 * (Real.pi : ℂ) * Complex.I) ^ k / (k.factorial : ℂ) * (bernoulliFun k x : ℂ)‖ = (2 * Real.pi) ^ k / (k.factorial : ℝ) * |bernoulliFun k x|`. Rewrite using `[norm_mul, norm_div, norm_neg, norm_pow, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one, Complex.norm_two]`. Rewrite using `[← hnorm]`.

Use `hbound.trans ?_` and prove the remaining obligations. Use polynomial arithmetic with `[Real.pi_pos, Real.pi_lt_d2]`.
-/
private theorem polybound_big {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (2 * Real.pi) ^ k / (k.factorial : ℝ) * |bernoulliFun k x| ≤ 4 := by
  have hs := hasSum_one_div_nat_pow_mul_fourier hk hx
  have h2 : ∀ (m : ℤ) (y : UnitAddCircle), ‖fourier m y + (-1) ^ k * fourier (-m) y‖ ≤ 2 := by
    intro m y
    calc _ ≤ ‖fourier m y‖ + ‖(-1 : ℂ) ^ k * fourier (-m) y‖ := norm_add_le _ _
      _ = 2 := by
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, polybound_norm_fourier,
          polybound_norm_fourier]
        norm_num
  have hbound : ‖-(2 * (Real.pi : ℂ) * Complex.I) ^ k / (k.factorial : ℂ) * (bernoulliFun k x : ℂ)‖
      ≤ 2 * (Real.pi ^ 2 / 6) := by
    rw [← hs.tsum_eq]
    refine tsum_of_norm_bounded (hasSum_zeta_two.mul_left 2) fun n ↦ ?_
    rw [norm_mul]
    have h1 : ‖1 / (n : ℂ) ^ k‖ ≤ 1 / (n : ℝ) ^ 2 := by
      rw [norm_div, norm_one, norm_pow, Complex.norm_natCast]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [zero_pow (by omega : k ≠ 0)]
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hn1 hk)
    calc _ ≤ 1 / (n : ℝ) ^ 2 * 2 := mul_le_mul h1 (h2 _ _) (norm_nonneg _) (by positivity)
      _ = 2 * (1 / (n : ℝ) ^ 2) := mul_comm _ _
  have hnorm : ‖-(2 * (Real.pi : ℂ) * Complex.I) ^ k / (k.factorial : ℂ) * (bernoulliFun k x : ℂ)‖
      = (2 * Real.pi) ^ k / (k.factorial : ℝ) * |bernoulliFun k x| := by
    rw [norm_mul, norm_div, norm_neg, norm_pow, norm_mul, norm_mul, Complex.norm_I,
      Complex.norm_real, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one, Complex.norm_two]
  rw [← hnorm]
  refine hbound.trans ?_
  nlinarith [Real.pi_pos, Real.pi_lt_d2]

/- English proof (translation)
Introduce `k x h0 h1`. Establish `hx0 : (0 : ℝ) ≤ x` using `by exact_mod_cast h0`. Establish `hx1 : (x : ℝ) ≤ 1` using `by exact_mod_cast h1`. Establish `hpi : (0 : ℝ) < 2 * Real.pi` using `by positivity`. Break down `lt_or_ge k 2 with hk | hk` into its components or cases.

Use `interval_cases k`. Simplify using `[Polynomial.bernoulli_zero]`. Simplify using `only [Polynomial.bernoulli_one, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Nat.factorial_one, Nat.cast_one, pow_one]`. Establish `key : |(x : ℝ) - 1 / 2| ≤ 1 / 2` using `abs_le.mpr ⟨by linarith, by linarith⟩`. Establish `: (1 : ℝ) / 2 ≤ 4 * 1 / (2 * Real.pi)`.

Rewrite using `[le_div_iff₀ hpi]`. Use polynomial arithmetic with `[Real.pi_lt_d2]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb` using `polybound_big hk (x := (x : ℝ)) ⟨hx0, hx1⟩`. Rewrite using `[polybound_cast]`.

Establish `hf : (0 : ℝ) < k.factorial` using `by exact_mod_cast Nat.factorial_pos k`. Rewrite `hb` using `[div_mul_eq_mul_div, div_le_iff₀ hf]`. Rewrite using `[le_div_iff₀ (pow_pos hpi k)]`. Combine the linear relations using `[mul_comm (|bernoulliFun k x|) ((2 * Real.pi) ^ k)]`.
-/
theorem UpperTheory.V.Bern.b_polybound :
    ∀ (k : ℕ) (x : ℚ), 0 ≤ x → x ≤ 1 → |(((Polynomial.bernoulli k).eval x : ℚ) : ℝ)| ≤ 4 * (k.factorial : ℝ) / (2 * Real.pi) ^ k := by
  intro k x h0 h1
  have hx0 : (0 : ℝ) ≤ x := by exact_mod_cast h0
  have hx1 : (x : ℝ) ≤ 1 := by exact_mod_cast h1
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rcases lt_or_ge k 2 with hk | hk
  · interval_cases k
    · simp [Polynomial.bernoulli_zero]
    · simp only [Polynomial.bernoulli_one, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
        Nat.factorial_one, Nat.cast_one, pow_one]
      have key : |(x : ℝ) - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      have : (1 : ℝ) / 2 ≤ 4 * 1 / (2 * Real.pi) := by
        rw [le_div_iff₀ hpi]
        nlinarith [Real.pi_lt_d2]
      linarith
  · have hb := polybound_big hk (x := (x : ℝ)) ⟨hx0, hx1⟩
    rw [polybound_cast]
    have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    rw [div_mul_eq_mul_div, div_le_iff₀ hf] at hb
    rw [le_div_iff₀ (pow_pos hpi k)]
    linarith [mul_comm (|bernoulliFun k x|) ((2 * Real.pi) ^ k)]

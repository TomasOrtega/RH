import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

/- English proof (translation)
Use `set q := Function.Periodic.qParam 1 (τ : ℂ) with hqdef`. Establish `hqe : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ) = q`. Simplify using `[hqdef, Function.Periodic.qParam]`. Establish `hq : ‖q‖ < 1`. Rewrite using `[hqdef, Function.Periodic.norm_qParam]`.

Use `(Real.exp_lt_exp.mpr ?_).trans_eq Real.exp_zero` and prove the remaining obligations. Use `τ.im_pos` as an intermediate fact. Use `Real.pi_pos` as an intermediate fact. Simplify using `only [UpperHalfPlane.coe_im, div_one]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hσ : ∀ n : ℕ, ‖((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ n‖ ≤ (n : ℝ) ^ k * ‖q‖ ^ n`. Introduce `n`. Rewrite using `[norm_mul, norm_pow, Complex.norm_natCast]`. Use `gcongr`. Rewrite using `[ArithmeticFunction.sigma_apply]`.

Use `push_cast`. Combine the equalities or inequalities in the displayed calculation. Conclude with `Nat.card_divisors_le_self n` after adjusting the coercions. Use `_ = (n : ℝ) ^ k := by`. Rewrite using `[← pow_succ']`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `hsum : Summable fun n : ℕ => ((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ n` using `Summable.of_norm_bounded (summable_pow_mul_geometric_of_norm_lt_one k (by simpa using hq)) hσ`. Establish `hsum1 : Summable fun n : ℕ => ((ArithmeticFunction.sigma (k - 1) (n + 1) : ℕ) : ℂ) * q ^ (n + 1)` using `(summable_nat_add_iff 1).mpr hsum`. Establish `hE` using `EisensteinSeries.q_expansion_riemannZeta hk hke τ`.

Rewrite using `[hE, hC, hqe]`. Rewrite using `[← hasSum_nat_add_iff' 1]`. Simplify using `only [Finset.range_one, Finset.sum_singleton, pow_zero, if_true, mul_one, add_sub_cancel_left, Nat.add_eq_zero, one_ne_zero, and_false, if_false]`. Establish `ht : ∑' n : ℕ+, ((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ (n : ℕ) = ∑' n : ℕ, ((ArithmeticFunction.sigma (k - 1) (n + 1) : ℕ) : ℂ) * q ^ (n + 1)` using `tsum_pnat_eq_tsum_succ (f := fun n => ((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ n)`. Apply the tactic sequence `convert hsum1.hasSum.mul_left C using 1 <;> first`.

Consider the case `rfl`. Consider the case `(funext n <;> ring)`. Consider the case `(congr 1 <;> (rw [← ht]; apply tsum_congr; intro n; simp))`.
-/
private theorem hasSum_sigma_mul_qParam_pow_modularForm_E {k : ℕ} (hk : 3 ≤ k) (hke : Even k) (C : ℂ)
    (hC : (riemannZeta k)⁻¹ * (-2 * (Real.pi : ℂ) * Complex.I) ^ k / ((k - 1).factorial : ℂ) = C)
    (τ : ℍ) :
    HasSum (fun m : ℕ => (if m = 0 then (1 : ℂ) else C * (ArithmeticFunction.sigma (k - 1) m : ℂ)) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (ModularForm.E hk τ) := by
  set q := Function.Periodic.qParam 1 (τ : ℂ) with hqdef
  have hqe : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ) = q := by
    simp [hqdef, Function.Periodic.qParam]
  have hq : ‖q‖ < 1 := by
    rw [hqdef, Function.Periodic.norm_qParam]
    refine (Real.exp_lt_exp.mpr ?_).trans_eq Real.exp_zero
    have := τ.im_pos
    have := Real.pi_pos
    simp only [UpperHalfPlane.coe_im, div_one]
    nlinarith
  have hσ : ∀ n : ℕ, ‖((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ n‖ ≤ (n : ℝ) ^ k * ‖q‖ ^ n := by
    intro n
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    gcongr
    rw [ArithmeticFunction.sigma_apply]
    push_cast
    calc ∑ d ∈ n.divisors, (d : ℝ) ^ (k - 1) ≤ ∑ d ∈ n.divisors, (n : ℝ) ^ (k - 1) :=
          Finset.sum_le_sum fun d hd => pow_le_pow_left₀ (by positivity)
            (by exact_mod_cast Nat.divisor_le hd) _
      _ = (n.divisors.card : ℝ) * (n : ℝ) ^ (k - 1) := by simp
      _ ≤ (n : ℝ) * (n : ℝ) ^ (k - 1) := by
          gcongr
          exact_mod_cast Nat.card_divisors_le_self n
      _ = (n : ℝ) ^ k := by
          rw [← pow_succ']
          congr 1
          omega
  have hsum : Summable fun n : ℕ => ((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ n :=
    Summable.of_norm_bounded (summable_pow_mul_geometric_of_norm_lt_one k (by simpa using hq)) hσ
  have hsum1 : Summable fun n : ℕ =>
      ((ArithmeticFunction.sigma (k - 1) (n + 1) : ℕ) : ℂ) * q ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr hsum
  have hE := EisensteinSeries.q_expansion_riemannZeta hk hke τ
  rw [hE, hC, hqe]
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, if_true, mul_one,
    add_sub_cancel_left, Nat.add_eq_zero, one_ne_zero, and_false, if_false]
  have ht : ∑' n : ℕ+, ((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ (n : ℕ) =
      ∑' n : ℕ, ((ArithmeticFunction.sigma (k - 1) (n + 1) : ℕ) : ℂ) * q ^ (n + 1) :=
    tsum_pnat_eq_tsum_succ (f := fun n => ((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ n)
  convert hsum1.hasSum.mul_left C using 1 <;>
    first
    | rfl
    | (funext n <;> ring)
    | (congr 1 <;> (rw [← ht]; apply tsum_congr; intro n; simp))

/- English proof (translation)
Establish `hE : E₄ = ModularForm.E (k` using `4) (by norm_num) := rfl`. Use extensionality with `m`. Use `ModularFormClass.qExpansion_coeff_unique (f := E₄) (h := 1) (c := fun m => PowerSeries.coeff m (e4Z.map (Int.castRingHom ℂ))) one_pos (by simp) ?_ m` and prove the remaining obligations. Introduce `τ`. Establish `hC : (riemannZeta ((4 : ℕ) : ℂ))⁻¹ * (-2 * (Real.pi : ℂ) * Complex.I) ^ 4 / (((4 - 1).factorial : ℕ) : ℂ) = 240`.

Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Rewrite using `[show ((4 : ℕ) : ℂ) = 4 by norm_num, riemannZeta_four]`. Establish `hI : Complex.I ^ 4 = 1` using `Complex.I_pow_four`. Simplify using `only [Nat.factorial, Nat.succ_eq_add_one]`. Clear the denominators using the available nonvanishing facts.

Put the polynomial expressions in normal form. Rewrite using `[hI]`. Expand and normalize the polynomial expressions, which then agree. Establish `h` using `hasSum_sigma_mul_qParam_pow_modularForm_E (k := 4) (by norm_num) (by decide) 240 hC τ`. Rewrite using `[hE]`.

Use `h using 2 with n` and compare the differences between its conclusion and the goal. Simplify using `only [e4Z, PowerSeries.coeff_map, PowerSeries.coeff_mk]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem map_eisensteinFourInt : e4Z.map (Int.castRingHom ℂ) = qExpansion 1 E₄ := by
  have hE : E₄ = ModularForm.E (k := 4) (by norm_num) := rfl
  ext m
  refine ModularFormClass.qExpansion_coeff_unique (f := E₄) (h := 1)
    (c := fun m => PowerSeries.coeff m (e4Z.map (Int.castRingHom ℂ))) one_pos (by simp) ?_ m
  intro τ
  have hC : (riemannZeta ((4 : ℕ) : ℂ))⁻¹ * (-2 * (Real.pi : ℂ) * Complex.I) ^ 4 /
      (((4 - 1).factorial : ℕ) : ℂ) = 240 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [show ((4 : ℕ) : ℂ) = 4 by norm_num, riemannZeta_four]
    have hI : Complex.I ^ 4 = 1 := Complex.I_pow_four
    simp only [Nat.factorial, Nat.succ_eq_add_one]
    field_simp
    ring_nf
    rw [hI]
    ring
  have h := hasSum_sigma_mul_qParam_pow_modularForm_E (k := 4) (by norm_num) (by decide) 240 hC τ
  rw [hE]
  convert h using 2 with n
  simp only [e4Z, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs <;> simp

/- English proof (translation)
Establish `hE : E₆ = ModularForm.E (k` using `6) (by norm_num) := rfl`. Use extensionality with `m`. Use `ModularFormClass.qExpansion_coeff_unique (f := E₆) (h := 1) (c := fun m => PowerSeries.coeff m (e6Z.map (Int.castRingHom ℂ))) one_pos (by simp) ?_ m` and prove the remaining obligations. Introduce `τ`. Establish `hb6 : bernoulli 6 = 1 / 42`.

Establish `h5 : bernoulli' 5 = 0`. Rewrite using `[bernoulli'_def]`. Evaluate the numerical expressions using `[Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four, Nat.choose]`. Rewrite using `[bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]`. Evaluate the numerical expressions using `[Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four, h5, Nat.choose]`.

Establish `hz6 : riemannZeta ((6 : ℕ) : ℂ) = (Real.pi : ℂ) ^ 6 / 945`. Establish `h6` using `riemannZeta_two_mul_nat (k := 3) (by norm_num)`. Rewrite using `[show ((6 : ℕ) : ℂ) = 2 * ((3 : ℕ) : ℂ) by norm_num, h6, hb6]`. Evaluate the numerical expressions using `[Nat.factorial]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hC : (riemannZeta ((6 : ℕ) : ℂ))⁻¹ * (-2 * (Real.pi : ℂ) * Complex.I) ^ 6 / (((6 - 1).factorial : ℕ) : ℂ) = -504`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Rewrite using `[hz6]`. Establish `hI : Complex.I ^ 6 = -1`. Rewrite using `[show (6 : ℕ) = 2 * 3 by rfl, pow_mul, Complex.I_sq]`.

Evaluate the numerical expressions. Simplify using `only [Nat.factorial, Nat.succ_eq_add_one]`. Clear the denominators using the available nonvanishing facts. Put the polynomial expressions in normal form. Rewrite using `[hI]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h` using `hasSum_sigma_mul_qParam_pow_modularForm_E (k := 6) (by norm_num) (by decide) (-504) hC τ`. Rewrite using `[hE]`. Use `h using 2 with n` and compare the differences between its conclusion and the goal. Simplify using `only [e6Z, PowerSeries.coeff_map, PowerSeries.coeff_mk]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem map_eisensteinSixInt : e6Z.map (Int.castRingHom ℂ) = qExpansion 1 E₆ := by
  have hE : E₆ = ModularForm.E (k := 6) (by norm_num) := rfl
  ext m
  refine ModularFormClass.qExpansion_coeff_unique (f := E₆) (h := 1)
    (c := fun m => PowerSeries.coeff m (e6Z.map (Int.castRingHom ℂ))) one_pos (by simp) ?_ m
  intro τ
  have hb6 : bernoulli 6 = 1 / 42 := by
    have h5 : bernoulli' 5 = 0 := by
      rw [bernoulli'_def]
      norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
        bernoulli'_three, bernoulli'_four, Nat.choose]
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
    norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
      bernoulli'_three, bernoulli'_four, h5, Nat.choose]
  have hz6 : riemannZeta ((6 : ℕ) : ℂ) = (Real.pi : ℂ) ^ 6 / 945 := by
    have h6 := riemannZeta_two_mul_nat (k := 3) (by norm_num)
    rw [show ((6 : ℕ) : ℂ) = 2 * ((3 : ℕ) : ℂ) by norm_num, h6, hb6]
    norm_num [Nat.factorial]
    ring
  have hC : (riemannZeta ((6 : ℕ) : ℂ))⁻¹ * (-2 * (Real.pi : ℂ) * Complex.I) ^ 6 /
      (((6 - 1).factorial : ℕ) : ℂ) = -504 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [hz6]
    have hI : Complex.I ^ 6 = -1 := by
      rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, Complex.I_sq]
      norm_num
    simp only [Nat.factorial, Nat.succ_eq_add_one]
    field_simp
    ring_nf
    rw [hI]
    ring
  have h := hasSum_sigma_mul_qParam_pow_modularForm_E (k := 6) (by norm_num) (by decide) (-504) hC τ
  rw [hE]
  convert h using 2 with n
  simp only [e6Z, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs <;> simp

/- English proof (translation)
Establish `h1 : AnalyticAt ℂ (cuspFunction 1 ⇑E₄) 0` using `ModularFormClass.analyticAt_cuspFunction_zero E₄ one_pos (by simp)`. Establish `h2 : AnalyticAt ℂ (cuspFunction 1 (⇑E₄ * ⇑E₄)) 0`. Establish `h3` using `ModularFormClass.analyticAt_cuspFunction_zero (E₄.mul E₄) one_pos (by simp)`. Rewrite `h3` using `[ModularForm.coe_mul]`. Then use the resulting hypothesis. Establish `hA : AA = ⇑E₄ * (⇑E₄ * ⇑E₄)`.

Use function extensionality and compare the values at `τ`. Simplify using `only [AA, Pi.mul_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hA, qExpansion_mul h1 h2, qExpansion_mul h1 h1, ← map_eisensteinFourInt]`. Simplify using `only [aC, aZ, map_pow]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem aC_eq : aC = qExpansion 1 AA := by
  have h1 : AnalyticAt ℂ (cuspFunction 1 ⇑E₄) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero E₄ one_pos (by simp)
  have h2 : AnalyticAt ℂ (cuspFunction 1 (⇑E₄ * ⇑E₄)) 0 := by
    have h3 := ModularFormClass.analyticAt_cuspFunction_zero (E₄.mul E₄) one_pos (by simp)
    rwa [ModularForm.coe_mul] at h3
  have hA : AA = ⇑E₄ * (⇑E₄ * ⇑E₄) := by
    funext τ
    simp only [AA, Pi.mul_apply]
    ring
  rw [hA, qExpansion_mul h1 h2, qExpansion_mul h1 h1, ← map_eisensteinFourInt]
  simp only [aC, aZ, map_pow]
  ring

end ReciprocityTheory.ChartRestriction.L1

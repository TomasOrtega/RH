import Formalism.ZeroFreeRegion.SmallHeightLogDeriv

open Complex MeasureTheory

noncomputable section

namespace Formalism.ZF

/- English proof (translation)
Establish `hSm : MeasurableSet ((Set.Ioc (-T) T)ᶜ)` using `measurableSet_Ioc.compl`. Establish `hg_int : Integrable (fun t : ℝ => 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹)` using `(integrable_inv_one_add_sq.comp_div hT.ne').const_mul _`. Establish `hbound : ∀ t ∈ (Set.Ioc (-T) T)ᶜ, ‖f t‖ ≤ 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹`. Introduce `t ht`. Establish `hTt : T ≤ |t|`.

Simplify using `only [Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at ht`. Break down `ht with h | h` into its components or cases. Rewrite using `[abs_of_neg (by linarith)]; linarith`. Rewrite using `[abs_of_pos (by linarith)]; linarith`. Establish `ht2 : T ^ 2 ≤ t ^ 2`.

Use `pow_le_pow_left₀ hT.le hTt 2` as an intermediate fact. Rewrite `this` using `[sq_abs]`. Then use the resulting hypothesis. Establish `htpos : 0 < t ^ 2` using `lt_of_lt_of_le (by positivity) ht2`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ = 2 * B / (T ^ 2 + t ^ 2) by field_simp]`.

Rewrite using `[div_le_div_iff₀ htpos (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h1 : ‖∫ t in (Set.Ioc (-T) T)ᶜ, f t‖ ≤ ∫ t in (Set.Ioc (-T) T)ᶜ, 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹` using `norm_integral_le_of_norm_le hg_int.integrableOn (ae_restrict_of_forall_mem hSm hbound)`. Establish `h2 : ∫ t in (Set.Ioc (-T) T)ᶜ, 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ ≤ ∫ t, 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹` using `setIntegral_le_integral hg_int (Filter.Eventually.of_forall (fun t => by positivity))`. Establish `h3 : ∫ t, 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ = 2 * Real.pi * B / T`.

Rewrite using `[integral_const_mul]`. Establish `e` using `MeasureTheory.Measure.integral_comp_div (fun x : ℝ => (1 + x ^ 2)⁻¹) T`. Rewrite using `[e, integral_univ_inv_one_add_sq, abs_of_pos hT]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_integral_compl_le (f : ℝ → ℂ) (B T : ℝ) (hB : 0 ≤ B) (hT : 0 < T)
    (hf : ∀ t : ℝ, T ≤ |t| → ‖f t‖ ≤ B / t ^ 2) :
    ‖∫ t in (Set.Ioc (-T) T)ᶜ, f t‖ ≤ 2 * Real.pi * B / T := by
  have hSm : MeasurableSet ((Set.Ioc (-T) T)ᶜ) := measurableSet_Ioc.compl
  have hg_int : Integrable (fun t : ℝ => 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.comp_div hT.ne').const_mul _
  have hbound : ∀ t ∈ (Set.Ioc (-T) T)ᶜ, ‖f t‖ ≤ 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ := by
    intro t ht
    have hTt : T ≤ |t| := by
      simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at ht
      rcases ht with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have ht2 : T ^ 2 ≤ t ^ 2 := by
      have := pow_le_pow_left₀ hT.le hTt 2
      rwa [sq_abs] at this
    have htpos : 0 < t ^ 2 := lt_of_lt_of_le (by positivity) ht2
    calc ‖f t‖ ≤ B / t ^ 2 := hf t hTt
      _ ≤ 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ := by
        rw [show 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ = 2 * B / (T ^ 2 + t ^ 2) by
          field_simp]
        rw [div_le_div_iff₀ htpos (by positivity)]
        nlinarith
  have h1 : ‖∫ t in (Set.Ioc (-T) T)ᶜ, f t‖ ≤ ∫ t in (Set.Ioc (-T) T)ᶜ, 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ :=
    norm_integral_le_of_norm_le hg_int.integrableOn (ae_restrict_of_forall_mem hSm hbound)
  have h2 : ∫ t in (Set.Ioc (-T) T)ᶜ, 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ ≤
      ∫ t, 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ :=
    setIntegral_le_integral hg_int (Filter.Eventually.of_forall (fun t => by positivity))
  have h3 : ∫ t, 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ = 2 * Real.pi * B / T := by
    rw [integral_const_mul]
    have e := MeasureTheory.Measure.integral_comp_div (fun x : ℝ => (1 + x ^ 2)⁻¹) T
    rw [e, integral_univ_inv_one_add_sq, abs_of_pos hT]
    field_simp
    ring
  linarith

/- English proof (translation)
Establish `hs0 : 0 ≤ c * s / 8` using `by positivity`. Establish `hA : 0 < Real.exp (-(c / 8) * s)` using `Real.exp_pos _`. Establish `hEA : Real.exp (c * s / 8) * Real.exp (-(c / 8) * s) = 1`. Rewrite using `[← Real.exp_add, show c * s / 8 + -(c / 8) * s = 0 by ring, Real.exp_zero]`. Establish `hsq : Real.exp (-(c * s / 4)) = Real.exp (-(c / 8) * s) ^ 2`.

Rewrite using `[← Real.exp_nat_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hfact : (c * s / 8) ^ 3 ≤ 6 * Real.exp (c * s / 8)`.

Establish `h` using `Real.pow_div_factorial_le_exp (c * s / 8) hs0 3`. Evaluate the numerical expressions using `[Nat.factorial] at h`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hkey : (c * s / 8) ^ 3 * Real.exp (-(c / 8) * s) ≤ 6`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hfact hA.le]`.

Establish `hs3 : s ^ 3 = (8 / c) ^ 3 * (c * s / 8) ^ 3`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hsq, hs3]`. Establish `hk : 0 < (8 / c) ^ 3` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem pow_three_mul_exp_le (c s : ℝ) (hc : 0 < c) (hs : 0 ≤ s) :
    s ^ 3 * Real.exp (-(c * s / 4)) ≤ 6 * (8 / c) ^ 3 * Real.exp (-(c / 8) * s) := by
  have hs0 : 0 ≤ c * s / 8 := by positivity
  have hA : 0 < Real.exp (-(c / 8) * s) := Real.exp_pos _
  have hEA : Real.exp (c * s / 8) * Real.exp (-(c / 8) * s) = 1 := by
    rw [← Real.exp_add, show c * s / 8 + -(c / 8) * s = 0 by ring, Real.exp_zero]
  have hsq : Real.exp (-(c * s / 4)) = Real.exp (-(c / 8) * s) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hfact : (c * s / 8) ^ 3 ≤ 6 * Real.exp (c * s / 8) := by
    have h := Real.pow_div_factorial_le_exp (c * s / 8) hs0 3
    norm_num [Nat.factorial] at h
    linarith
  have hkey : (c * s / 8) ^ 3 * Real.exp (-(c / 8) * s) ≤ 6 := by
    nlinarith [mul_le_mul_of_nonneg_right hfact hA.le]
  have hs3 : s ^ 3 = (8 / c) ^ 3 * (c * s / 8) ^ 3 := by
    field_simp
  rw [hsq, hs3]
  have hk : 0 < (8 / c) ^ 3 := by positivity
  calc (8 / c) ^ 3 * (c * s / 8) ^ 3 * Real.exp (-(c / 8) * s) ^ 2
      = (8 / c) ^ 3 * ((c * s / 8) ^ 3 * Real.exp (-(c / 8) * s)) * Real.exp (-(c / 8) * s) := by ring
    _ ≤ (8 / c) ^ 3 * 6 * Real.exp (-(c / 8) * s) := by gcongr
    _ = 6 * (8 / c) ^ 3 * Real.exp (-(c / 8) * s) := by ring

/- English proof (translation)
Establish `hcs : 8 ≤ c * s`. Rewrite `hs` using `[div_le_iff₀ hc]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hE1 : 1 ≤ Real.exp (c * s / 4)` using `Real.one_le_exp (by linarith)`. Establish `hE2 : Real.exp 2 ≤ Real.exp (c * s / 4)` using `Real.exp_le_exp.mpr (by linarith)`.

Establish `he2 : (2 : ℝ) ≤ Real.exp 2`. Use `Real.add_one_le_exp (2 : ℝ)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨hE1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Real.le_log_iff_exp_le (by positivity)]`.

Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Real.log_le_iff_le_exp (by positivity)]`. Establish `e : Real.exp (c * s / 2) = Real.exp (c * s / 4) ^ 2`. Rewrite using `[← Real.exp_nat_mul]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem log_exp_add_two_bounds (c s : ℝ) (hc : 0 < c) (hs : 8 / c ≤ s) :
    1 ≤ Real.exp (c * s / 4) ∧ 1 ≤ Real.log (Real.exp (c * s / 4) + 2) ∧
      Real.log (Real.exp (c * s / 4) + 2) ≤ c * s / 2 := by
  have hcs : 8 ≤ c * s := by
    rw [div_le_iff₀ hc] at hs
    linarith
  have hE1 : 1 ≤ Real.exp (c * s / 4) := Real.one_le_exp (by linarith)
  have hE2 : Real.exp 2 ≤ Real.exp (c * s / 4) := Real.exp_le_exp.mpr (by linarith)
  have he2 : (2 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  refine ⟨hE1, ?_, ?_⟩
  · rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  · rw [Real.log_le_iff_le_exp (by positivity)]
    have e : Real.exp (c * s / 2) = Real.exp (c * s / 4) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [e]
    nlinarith

/- English proof (translation)
Establish `hy' : y = Real.exp (s ^ 2)` using `by rw [← hℓ, Real.exp_log hy]`. Rewrite using `[Real.rpow_def_of_pos hy, hℓ]`. Use `conv_rhs => rw [hy']`. Rewrite using `[← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]`. Establish `key : c * s / 2 ≤ s ^ 2 * (c / L)`.

Rewrite using `[show s ^ 2 * (c / L) = (c * s ^ 2) / L by ring, le_div_iff₀ hL]`. Establish `hcs : 0 < c * s` using `mul_pos hc hs`. Establish `hL4 : L ≤ s` using `by nlinarith`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hL4 hcs.le]`. Use polynomial arithmetic with `[key]`.
-/
theorem exp_mul_rpow_le (y c L s : ℝ) (hy : 0 < y) (hℓ : Real.log y = s ^ 2) (hc : 0 < c)
    (hc2 : c ≤ 1 / 2) (hL : 0 < L) (hLs : L ≤ c * s / 2) (hs : 0 < s) :
    Real.exp (c * s / 4) * y ^ (1 - c / L) ≤ y * Real.exp (-(c * s / 4)) := by
  have hy' : y = Real.exp (s ^ 2) := by rw [← hℓ, Real.exp_log hy]
  rw [Real.rpow_def_of_pos hy, hℓ]
  conv_rhs => rw [hy']
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have key : c * s / 2 ≤ s ^ 2 * (c / L) := by
    rw [show s ^ 2 * (c / L) = (c * s ^ 2) / L by ring, le_div_iff₀ hL]
    have hcs : 0 < c * s := mul_pos hc hs
    have hL4 : L ≤ s := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hL4 hcs.le]
  nlinarith [key]

end Formalism.ZF

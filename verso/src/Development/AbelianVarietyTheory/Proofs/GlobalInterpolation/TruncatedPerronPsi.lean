import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TruncatedPerronKernel
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.PerronPsi

/- English proof (translation)
Take `⟨C, hC, hK⟩` from `GlobalTheory.PerronKernel.truncated_perron_kernel`. Use `⟨max C 1, lt_max_of_lt_right one_pos, ?_⟩` and prove the remaining obligations. Introduce `y c T hy hc hT`. Establish `hyc : 0 < y ^ c` using `Real.rpow_pos_of_pos hy c`. Distinguish the cases in `hy1 : y = 1`.

Substitute `hy1` using the available equality. Establish `hI : ∫ t in (-T)..T, ((1 : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) = ((2 * Real.arctan (T / c) : ℝ) : ℂ)`. Rewrite using `[← GlobalTheory.PerronKernel.vinv hc.ne' T]`. Use `congr 1`. Use extensionality with `t`.

Rewrite using `[Complex.ofReal_one, Complex.one_cpow, one_div]`. Establish `ha0 : 0 < Real.arctan (T / c)` using `Real.arctan_pos.2 (by positivity)`. Establish `ha1 : Real.arctan (T / c) < Real.pi / 2` using `Real.arctan_lt_pi_div_two _`. Establish `hpi` using `Real.pi_pos`. Establish `hE : ‖(1 / (2 * Real.pi) : ℂ) * ((2 * Real.arctan (T / c) : ℝ) : ℂ) - (if (1 : ℝ) ≤ 1 then 1 else 0)‖ ≤ 1`.

Rewrite using `[if_pos le_rfl]`. Establish `hre : (1 / (2 * Real.pi) : ℂ) * ((2 * Real.arctan (T / c) : ℝ) : ℂ) - 1 = ((Real.arctan (T / c) / Real.pi - 1 : ℝ) : ℂ)`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hre, Complex.norm_real, Real.norm_eq_abs, abs_le]`.

Establish `h1 : 0 ≤ Real.arctan (T / c) / Real.pi` using `div_nonneg ha0.le hpi.le`. Establish `h2 : Real.arctan (T / c) / Real.pi ≤ 1`. Rewrite using `[div_le_one hpi]`. Combine the linear equalities and inequalities to obtain the conclusion. Apply the tactic sequence `constructor <;> linarith`.

Rewrite using `[hI]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.one_rpow, mul_one]`. Conclude with `le_max_right _ _`.

Rewrite using `[Real.log_one, abs_zero, mul_zero, mul_zero]`. Check the signs of the components of the expression. Establish `hif : (if 1 ≤ y then (1 : ℂ) else 0) = (if 1 < y then 1 else 0)`. Distinguish the cases in `h : 1 < y`. Simplify using `[h, h.le]`.

Establish `h' : ¬ 1 ≤ y` using `fun h' => h (lt_of_le_of_ne h' (Ne.symm hy1))`. Simplify using `[h, h']`. Establish `hK'` using `hK y c T hy hy1 hc hT`. Rewrite using `[hif]`. Establish `hL : 0 < T * |Real.log y|` using `mul_pos (by linarith) (abs_pos.2 (Real.log_ne_zero_of_pos_of_ne_one hy hy1))`.

Establish `hC' : C ≤ max C 1` using `le_max_left _ _`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Conclude with `min_le_right _ _`.

Use `_ = C * y ^ c := by rw [mul_assoc, one_div_mul_cancel hL.ne', mul_one]`. Use `_ ≤ max C 1 * y ^ c := by gcongr`.
-/
lemma kernel_bound : ∃ C : ℝ, 0 < C ∧ ∀ y c T : ℝ, 0 < y → 0 < c → 1 ≤ T →
    ‖(1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))
      - (if 1 ≤ y then 1 else 0)‖ ≤ C * y ^ c ∧
    ‖(1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))
      - (if 1 ≤ y then 1 else 0)‖ * (T * |Real.log y|) ≤ C * y ^ c := by
  obtain ⟨C, hC, hK⟩ := GlobalTheory.PerronKernel.truncated_perron_kernel
  refine ⟨max C 1, lt_max_of_lt_right one_pos, ?_⟩
  intro y c T hy hc hT
  have hyc : 0 < y ^ c := Real.rpow_pos_of_pos hy c
  by_cases hy1 : y = 1
  · subst hy1
    have hI : ∫ t in (-T)..T, ((1 : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)
        = ((2 * Real.arctan (T / c) : ℝ) : ℂ) := by
      rw [← GlobalTheory.PerronKernel.vinv hc.ne' T]
      congr 1
      ext t
      rw [Complex.ofReal_one, Complex.one_cpow, one_div]
    have ha0 : 0 < Real.arctan (T / c) := Real.arctan_pos.2 (by positivity)
    have ha1 : Real.arctan (T / c) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have hpi := Real.pi_pos
    have hE : ‖(1 / (2 * Real.pi) : ℂ) * ((2 * Real.arctan (T / c) : ℝ) : ℂ)
        - (if (1 : ℝ) ≤ 1 then 1 else 0)‖ ≤ 1 := by
      rw [if_pos le_rfl]
      have hre : (1 / (2 * Real.pi) : ℂ) * ((2 * Real.arctan (T / c) : ℝ) : ℂ) - 1
          = ((Real.arctan (T / c) / Real.pi - 1 : ℝ) : ℂ) := by
        push_cast
        field_simp
      rw [hre, Complex.norm_real, Real.norm_eq_abs, abs_le]
      have h1 : 0 ≤ Real.arctan (T / c) / Real.pi := div_nonneg ha0.le hpi.le
      have h2 : Real.arctan (T / c) / Real.pi ≤ 1 := by
        rw [div_le_one hpi]
        linarith
      constructor <;> linarith
    rw [hI]
    refine ⟨?_, ?_⟩
    · calc _ ≤ (1 : ℝ) := hE
        _ ≤ max C 1 * (1 : ℝ) ^ c := by
          rw [Real.one_rpow, mul_one]
          exact le_max_right _ _
    · rw [Real.log_one, abs_zero, mul_zero, mul_zero]
      positivity
  · have hif : (if 1 ≤ y then (1 : ℂ) else 0) = (if 1 < y then 1 else 0) := by
      by_cases h : 1 < y
      · simp [h, h.le]
      · have h' : ¬ 1 ≤ y := fun h' => h (lt_of_le_of_ne h' (Ne.symm hy1))
        simp [h, h']
    have hK' := hK y c T hy hy1 hc hT
    rw [hif]
    have hL : 0 < T * |Real.log y| :=
      mul_pos (by linarith) (abs_pos.2 (Real.log_ne_zero_of_pos_of_ne_one hy hy1))
    have hC' : C ≤ max C 1 := le_max_left _ _
    refine ⟨?_, ?_⟩
    · calc _ ≤ C * y ^ c * min 1 (1 / (T * |Real.log y|)) := hK'
        _ ≤ C * y ^ c * 1 := by gcongr; exact min_le_left _ _
        _ ≤ max C 1 * y ^ c := by rw [mul_one]; gcongr
    · calc _ ≤ C * y ^ c * min 1 (1 / (T * |Real.log y|)) * (T * |Real.log y|) :=
            mul_le_mul_of_nonneg_right hK' hL.le
        _ ≤ C * y ^ c * (1 / (T * |Real.log y|)) * (T * |Real.log y|) := by
          gcongr
          exact min_le_right _ _
        _ = C * y ^ c := by rw [mul_assoc, one_div_mul_cancel hL.ne', mul_one]
        _ ≤ max C 1 * y ^ c := by gcongr

/- English proof (translation)
Establish `hsne : ∀ t : ℝ, (c : ℂ) + t * I ≠ 0` using `fun t => GlobalTheory.PerronKernel.ne_zero_of_re hc.ne'`. Establish `hsc : Continuous (fun t : ℝ => (c : ℂ) + t * I)` using `by fun_prop`. Establish `hre : ∀ t : ℝ, ((c : ℂ) + t * I).re = c` using `fun t => by simp`. Use `set F : ℕ → ℝ → ℂ := fun n t => LSeries.term a ((c : ℂ) + t * I) n * ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) with hF`. Establish `hsum_eq : ∀ n : ℕ, a n * ∫ t in (-T)..T, ((u / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) = ∫ t in (-T)..T, F n t`.

Introduce `n`. Rewrite using `[← intervalIntegral.integral_const_mul]`. Apply `intervalIntegral.integral_congr` to reduce the goal to its premises. Introduce `t _`. Simplify using `only [hF]`.

Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using `[ha0]`. Rewrite using `[LSeries.term_of_ne_zero hn]`. Establish `hn0 : (0 : ℝ) < n` using `by exact_mod_cast Nat.pos_of_ne_zero hn`. Establish `harg : ((n : ℝ) : ℂ).arg ≠ Real.pi`.

Rewrite using `[Complex.arg_ofReal_of_nonneg hn0.le]`. Conclude with `Real.pi_ne_zero.symm`. Establish `hdiv : (u / n : ℝ) = u * (n : ℝ)⁻¹` using `div_eq_mul_inv _ _`. Establish `hcp : ((u / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) = (u : ℂ) ^ ((c : ℂ) + t * I) / (n : ℂ) ^ ((c : ℂ) + t * I)`. Rewrite using `[hdiv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hu.le (inv_nonneg.2 hn0.le), Complex.ofReal_inv, Complex.inv_cpow _ _ harg, ← div_eq_mul_inv, Complex.ofReal_natCast]`.

Rewrite using `[hcp]`. Expand and normalize the polynomial expressions, which then agree. Establish `hS : ∀ t : ℝ, LSeriesSummable a ((c : ℂ) + t * I)` using `fun t => hs.of_re_le_re (by simp)`. Establish `hlim : ∀ t : ℝ, HasSum (fun n => F n t) (LSeries a ((c : ℂ) + t * I) * ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)))` using `fun t => HasSum.mul_right _ (hS t).LSeriesHasSum`. Establish `hbound : ∀ n t, ‖F n t‖ ≤ ‖LSeries.term a (c : ℂ) n‖ * (u ^ c / c)`.

Introduce `n t`. Simplify using `only [hF]`. Rewrite using `[norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hu, hre t, LSeries.norm_term_eq, LSeries.norm_term_eq, hre t, Complex.ofReal_re]`. Apply the tactic sequence `apply mul_le_mul_of_nonneg_left _ (by split_ifs <;> positivity)`. Establish `h1` using `Complex.re_le_norm ((c : ℂ) + t * I)`.

Rewrite `h1` using `[hre t]`. Conclude with `div_le_div_of_nonneg_left (by positivity) hc h1`. Establish `hcont : ∀ n, Continuous (F n)`. Introduce `n`. Simplify using `only [hF]`.

Establish `h2 : Continuous fun t : ℝ => (u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)` using `(hsc.const_cpow (Or.inl (by exact_mod_cast hu.ne'))).div hsc hsne`. Use `Continuous.mul ?_ h2` and prove the remaining obligations. Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using `only [LSeries.term_zero]`. Conclude with `continuous_const`.

Simplify using `only [LSeries.term_of_ne_zero hn]`. Conclude with `continuous_const.div (hsc.const_cpow (Or.inl (by exact_mod_cast hn))) (fun t => by simp [hn])`. Establish `key` using `intervalIntegral.hasSum_integral_of_dominated_convergence (μ := MeasureTheory.volume) (a := -T) (b := T) (F := F) (f := fun t => LSeries a ((c : ℂ) + t * I) * ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))) (fun n _ => ‖LSeries.term a (c : ℂ) n‖ * (u ^ c / c)) (fun n => (hcont …`. Establish `e1 : (fun n : ℕ => a n * ∫ t in (-T)..T, ((u / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) = fun n => ∫ t in (-T)..T, F n t` using `funext hsum_eq`. Establish `e2 : ∫ t in (-T)..T, LSeries a ((c : ℂ) + t * I) * (u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) = ∫ t in (-T)..T, LSeries a ((c : ℂ) + t * I) * ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))`.

Apply `intervalIntegral.integral_congr` to reduce the goal to its premises. Introduce `t _`. Simplify using `only`. Rewrite using `[mul_div_assoc]`. Rewrite using `[e1, e2]`.

Conclude with `key`.
-/
lemma interchange (a : ℕ → ℂ) (ha0 : a 0 = 0) {c u : ℝ} (T : ℝ) (hc : 0 < c) (hu : 0 < u)
    (hs : LSeriesSummable a c) :
    HasSum (fun n : ℕ => a n * ∫ t in (-T)..T,
        ((u / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))
      (∫ t in (-T)..T, LSeries a ((c : ℂ) + t * I) * (u : ℂ) ^ ((c : ℂ) + t * I)
        / ((c : ℂ) + t * I)) := by
  have hsne : ∀ t : ℝ, (c : ℂ) + t * I ≠ 0 := fun t => GlobalTheory.PerronKernel.ne_zero_of_re hc.ne'
  have hsc : Continuous (fun t : ℝ => (c : ℂ) + t * I) := by fun_prop
  have hre : ∀ t : ℝ, ((c : ℂ) + t * I).re = c := fun t => by simp
  set F : ℕ → ℝ → ℂ := fun n t => LSeries.term a ((c : ℂ) + t * I) n
    * ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) with hF
  have hsum_eq : ∀ n : ℕ, a n * ∫ t in (-T)..T,
      ((u / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) = ∫ t in (-T)..T, F n t := by
    intro n
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hF]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [ha0]
    · rw [LSeries.term_of_ne_zero hn]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have harg : ((n : ℝ) : ℂ).arg ≠ Real.pi := by
        rw [Complex.arg_ofReal_of_nonneg hn0.le]
        exact Real.pi_ne_zero.symm
      have hdiv : (u / n : ℝ) = u * (n : ℝ)⁻¹ := div_eq_mul_inv _ _
      have hcp : ((u / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I)
          = (u : ℂ) ^ ((c : ℂ) + t * I) / (n : ℂ) ^ ((c : ℂ) + t * I) := by
        rw [hdiv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hu.le (inv_nonneg.2 hn0.le),
          Complex.ofReal_inv, Complex.inv_cpow _ _ harg, ← div_eq_mul_inv, Complex.ofReal_natCast]
      rw [hcp]
      ring
  have hS : ∀ t : ℝ, LSeriesSummable a ((c : ℂ) + t * I) :=
    fun t => hs.of_re_le_re (by simp)
  have hlim : ∀ t : ℝ, HasSum (fun n => F n t)
      (LSeries a ((c : ℂ) + t * I) * ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))) :=
    fun t => HasSum.mul_right _ (hS t).LSeriesHasSum
  have hbound : ∀ n t, ‖F n t‖ ≤ ‖LSeries.term a (c : ℂ) n‖ * (u ^ c / c) := by
    intro n t
    simp only [hF]
    rw [norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hu, hre t, LSeries.norm_term_eq,
      LSeries.norm_term_eq, hre t, Complex.ofReal_re]
    apply mul_le_mul_of_nonneg_left _ (by split_ifs <;> positivity)
    have h1 := Complex.re_le_norm ((c : ℂ) + t * I)
    rw [hre t] at h1
    exact div_le_div_of_nonneg_left (by positivity) hc h1
  have hcont : ∀ n, Continuous (F n) := by
    intro n
    simp only [hF]
    have h2 : Continuous fun t : ℝ => (u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) :=
      (hsc.const_cpow (Or.inl (by exact_mod_cast hu.ne'))).div hsc hsne
    refine Continuous.mul ?_ h2
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [LSeries.term_zero]
      exact continuous_const
    · simp only [LSeries.term_of_ne_zero hn]
      exact continuous_const.div (hsc.const_cpow (Or.inl (by exact_mod_cast hn)))
        (fun t => by simp [hn])
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := MeasureTheory.volume)
    (a := -T) (b := T) (F := F)
    (f := fun t => LSeries a ((c : ℂ) + t * I) * ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)))
    (fun n _ => ‖LSeries.term a (c : ℂ) n‖ * (u ^ c / c))
    (fun n => (hcont n).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall (fun t _ => hbound n t))
    (Filter.Eventually.of_forall (fun _ _ => (summable_norm_iff.2 hs).mul_right _))
    intervalIntegrable_const
    (Filter.Eventually.of_forall (fun t _ => hlim t))
  have e1 : (fun n : ℕ => a n * ∫ t in (-T)..T,
      ((u / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))
      = fun n => ∫ t in (-T)..T, F n t := funext hsum_eq
  have e2 : ∫ t in (-T)..T, LSeries a ((c : ℂ) + t * I) * (u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)
      = ∫ t in (-T)..T, LSeries a ((c : ℂ) + t * I) * ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only
    rw [mul_div_assoc]
  rw [e1, e2]
  exact key

/- English proof (translation)
Establish `hs0 : 0 < s` using `by linarith`. Establish `hnn : ∀ n : ℕ, 0 ≤ 1 / (n : ℝ) ^ s` using `fun n => by positivity`. Establish `hI : ∀ a : ℕ, ∑ i ∈ Finset.range a, 1 / ((i : ℝ) + 1 + 1) ^ s ≤ 1 / (s - 1)`. Introduce `a`. Establish `hanti : AntitoneOn (fun x : ℝ => 1 / x ^ s) (Set.Icc 1 (1 + a))`.

Introduce `x hx y hy hxy`. Establish `hx0 : 0 < x` using `by linarith [hx.1]`. Conclude with `one_div_le_one_div_of_le (Real.rpow_pos_of_pos hx0 s) (Real.rpow_le_rpow hx0.le hxy hs0.le)`. Establish `h1` using `hanti.sum_le_integral`. Establish `h1a : (1 : ℝ) ≤ 1 + a`.

Use `(Nat.cast_nonneg a : (0 : ℝ) ≤ a)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsum : ∑ i ∈ Finset.range a, 1 / ((i : ℝ) + 1 + 1) ^ s = ∑ i ∈ Finset.range a, 1 / ((1 : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ s`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`.

Use `push_cast`. Put the polynomial expressions in normal form. Establish `hint : ∫ x in (1 : ℝ)..1 + a, 1 / x ^ s = ∫ x in (1 : ℝ)..1 + a, x ^ (-s)`. Apply `intervalIntegral.integral_congr` to reduce the goal to its premises. Introduce `x hx`.

Establish `hx0 : 0 < x`. Rewrite `hx` using `[Set.uIcc_of_le h1a]`. Combine the linear relations using `[hx.1]`. Simplify using `only`. Rewrite using `[Real.rpow_neg hx0.le, one_div]`.

Establish `h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (1 + a)`. Rewrite using `[Set.uIcc_of_le h1a]`. Introduce `h`. Combine the linear relations using `[h.1]`. Establish `hval : ∫ x in (1 : ℝ)..1 + a, x ^ (-s) = (1 - (1 + (a : ℝ)) ^ (1 - s)) / (s - 1)`.

Rewrite using `[integral_rpow (r := -s) (Or.inr ⟨fun h => by linarith, h0⟩), Real.one_rpow]`. Establish `: -s + 1 = 1 - s` using `by ring`. Rewrite using `[this]`. Establish `hs1 : s - 1 ≠ 0` using `by linarith`. Establish `hs2 : 1 - s ≠ 0` using `by linarith`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hpos : 0 ≤ (1 + (a : ℝ)) ^ (1 - s)` using `by positivity`. Rewrite using `[hsum]`. Combine the equalities or inequalities in the displayed calculation.

Apply `div_le_div_of_nonneg_right _ (by linarith)` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Apply `Real.tsum_le_of_sum_range_le hnn` to reduce the goal to its premises. Introduce `n`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_range_succ', Finset.sum_range_succ']`. Use `push_cast`. Rewrite using `[Real.zero_rpow hs0.ne', Real.one_rpow]`. Simplify using the standard rewrite rules. Use `_ ≤ 1 + 1 / (s - 1) := by linarith [hI n]`.
-/
lemma zeta_bound {s : ℝ} (hs : 1 < s) : ∑' n : ℕ, 1 / (n : ℝ) ^ s ≤ 1 + 1 / (s - 1) := by
  have hs0 : 0 < s := by linarith
  have hnn : ∀ n : ℕ, 0 ≤ 1 / (n : ℝ) ^ s := fun n => by positivity
  have hI : ∀ a : ℕ, ∑ i ∈ Finset.range a, 1 / ((i : ℝ) + 1 + 1) ^ s ≤ 1 / (s - 1) := by
    intro a
    have hanti : AntitoneOn (fun x : ℝ => 1 / x ^ s) (Set.Icc 1 (1 + a)) := by
      intro x hx y hy hxy
      have hx0 : 0 < x := by linarith [hx.1]
      exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hx0 s)
        (Real.rpow_le_rpow hx0.le hxy hs0.le)
    have h1 := hanti.sum_le_integral
    have h1a : (1 : ℝ) ≤ 1 + a := by
      have := (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
      linarith
    have hsum : ∑ i ∈ Finset.range a, 1 / ((i : ℝ) + 1 + 1) ^ s
        = ∑ i ∈ Finset.range a, 1 / ((1 : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ s := by
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      ring_nf
    have hint : ∫ x in (1 : ℝ)..1 + a, 1 / x ^ s = ∫ x in (1 : ℝ)..1 + a, x ^ (-s) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx0 : 0 < x := by
        rw [Set.uIcc_of_le h1a] at hx
        linarith [hx.1]
      simp only
      rw [Real.rpow_neg hx0.le, one_div]
    have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (1 + a) := by
      rw [Set.uIcc_of_le h1a]
      intro h
      linarith [h.1]
    have hval : ∫ x in (1 : ℝ)..1 + a, x ^ (-s) = (1 - (1 + (a : ℝ)) ^ (1 - s)) / (s - 1) := by
      rw [integral_rpow (r := -s) (Or.inr ⟨fun h => by linarith, h0⟩), Real.one_rpow]
      have : -s + 1 = 1 - s := by ring
      rw [this]
      have hs1 : s - 1 ≠ 0 := by linarith
      have hs2 : 1 - s ≠ 0 := by linarith
      field_simp
      ring
    have hpos : 0 ≤ (1 + (a : ℝ)) ^ (1 - s) := by positivity
    rw [hsum]
    calc _ ≤ _ := h1
      _ = (1 - (1 + (a : ℝ)) ^ (1 - s)) / (s - 1) := by rw [hint, hval]
      _ ≤ 1 / (s - 1) := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        linarith
  apply Real.tsum_le_of_sum_range_le hnn
  intro n
  calc ∑ i ∈ Finset.range n, 1 / (i : ℝ) ^ s
      ≤ ∑ i ∈ Finset.range (n + 2), 1 / (i : ℝ) ^ s :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
          (fun i _ _ => hnn i)
    _ = ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1 + 1) ^ s + 1 := by
        rw [Finset.sum_range_succ', Finset.sum_range_succ']
        push_cast
        rw [Real.zero_rpow hs0.ne', Real.one_rpow]
        simp
    _ ≤ 1 + 1 / (s - 1) := by linarith [hI n]

noncomputable def w (N : ℕ) (B : ℝ) (n : ℕ) : ℝ :=
  (if n = N then 1 else 0) + (if n = N + 1 then 1 else 0)
    + B * (1 / ((N - n : ℕ) : ℝ) + 1 / ((n - (N + 1) : ℕ) : ℝ))

/- English proof (translation)
Unfold `w`. Apply the tactic sequence `split_ifs <;> positivity`.
-/
lemma w_nonneg (N : ℕ) {B : ℝ} (hB : 0 ≤ B) (n : ℕ) : 0 ≤ w N B n := by
  unfold w
  split_ifs <;> positivity

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_range_succ']`. Simplify using `[harmonic]`. Use `_ ≤ 1 + Real.log N := harmonic_le_one_add_log N`.
-/
lemma harm (N : ℕ) : ∑ k ∈ Finset.range (N + 1), 1 / (k : ℝ) ≤ 1 + Real.log N := by
  calc ∑ k ∈ Finset.range (N + 1), 1 / (k : ℝ) = (harmonic N : ℝ) := by
        rw [Finset.sum_range_succ']
        simp [harmonic]
    _ ≤ 1 + Real.log N := harmonic_le_one_add_log N

/- English proof (translation)
Establish `hz1 : ∑ n ∈ Finset.range (N + 1 + (N + 1)), 1 / ((N - n : ℕ) : ℝ) = ∑ k ∈ Finset.range (N + 1), 1 / (k : ℝ)`. Rewrite using `[Finset.sum_range_add]`. Establish `h0 : ∑ x ∈ Finset.range (N + 1), 1 / ((N - (N + 1 + x) : ℕ) : ℝ) = 0`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `x _`.

Rewrite using `[show N - (N + 1 + x) = 0 by omega]`. Simplify using the standard rewrite rules. Rewrite using `[h0, add_zero]`. Use `Finset.sum_range_reflect (fun k : ℕ => 1 / (k : ℝ)) (N + 1)` as an intermediate fact. Simplify using `using this`.

Establish `hz2 : ∑ n ∈ Finset.range (N + 1 + (N + 1)), 1 / ((n - (N + 1) : ℕ) : ℝ) = ∑ k ∈ Finset.range (N + 1), 1 / (k : ℝ)`. Rewrite using `[Finset.sum_range_add]`. Establish `h0 : ∑ x ∈ Finset.range (N + 1), 1 / ((x - (N + 1) : ℕ) : ℝ) = 0`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `x hx`.

Rewrite `hx` using `[Finset.mem_range]`. Rewrite using `[show x - (N + 1) = 0 by omega]`. Simplify using the standard rewrite rules. Rewrite using `[h0, zero_add]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `x _`. Rewrite using `[show N + 1 + x - (N + 1) = x by omega]`. Establish `hsplit : ∑ n ∈ Finset.range (N + 1 + (N + 1)), w N B n = (∑ n ∈ Finset.range (N + 1 + (N + 1)), (if n = N then (1 : ℝ) else 0)) + (∑ n ∈ Finset.range (N + 1 + (N + 1)), (if n = N + 1 then (1 : ℝ) else 0)) + B * (∑ n ∈ Finset.range (N + 1 + (N + 1)), 1 / ((N - n : ℕ) : ℝ) + ∑ n ∈ …`. Simplify using `only [w, Finset.sum_add_distrib, mul_add, Finset.mul_sum]`. Rewrite using `[hsplit, hz1, hz2]`.

Simplify using `only [Finset.sum_ite_eq', Finset.mem_range, show N < N + 1 + (N + 1) by omega, show N + 1 < N + 1 + (N + 1) by omega, if_true]`. Establish `h` using `harm N`. Establish `h2` using `mul_le_mul_of_nonneg_left (show ∑ k ∈ Finset.range (N + 1), 1 / (k : ℝ) + ∑ k ∈ Finset.range (N + 1), 1 / (k : ℝ) ≤ 2 * (1 + Real.log N) by linarith) hB`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma sum_w (N : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    ∑ n ∈ Finset.range (N + 1 + (N + 1)), w N B n ≤ 2 + B * (2 * (1 + Real.log N)) := by
  have hz1 : ∑ n ∈ Finset.range (N + 1 + (N + 1)), 1 / ((N - n : ℕ) : ℝ)
      = ∑ k ∈ Finset.range (N + 1), 1 / (k : ℝ) := by
    rw [Finset.sum_range_add]
    have h0 : ∑ x ∈ Finset.range (N + 1), 1 / ((N - (N + 1 + x) : ℕ) : ℝ) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [show N - (N + 1 + x) = 0 by omega]
      simp
    rw [h0, add_zero]
    have := Finset.sum_range_reflect (fun k : ℕ => 1 / (k : ℝ)) (N + 1)
    simpa using this
  have hz2 : ∑ n ∈ Finset.range (N + 1 + (N + 1)), 1 / ((n - (N + 1) : ℕ) : ℝ)
      = ∑ k ∈ Finset.range (N + 1), 1 / (k : ℝ) := by
    rw [Finset.sum_range_add]
    have h0 : ∑ x ∈ Finset.range (N + 1), 1 / ((x - (N + 1) : ℕ) : ℝ) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [Finset.mem_range] at hx
      rw [show x - (N + 1) = 0 by omega]
      simp
    rw [h0, zero_add]
    apply Finset.sum_congr rfl
    intro x _
    rw [show N + 1 + x - (N + 1) = x by omega]
  have hsplit : ∑ n ∈ Finset.range (N + 1 + (N + 1)), w N B n
      = (∑ n ∈ Finset.range (N + 1 + (N + 1)), (if n = N then (1 : ℝ) else 0))
        + (∑ n ∈ Finset.range (N + 1 + (N + 1)), (if n = N + 1 then (1 : ℝ) else 0))
        + B * (∑ n ∈ Finset.range (N + 1 + (N + 1)), 1 / ((N - n : ℕ) : ℝ)
          + ∑ n ∈ Finset.range (N + 1 + (N + 1)), 1 / ((n - (N + 1) : ℕ) : ℝ)) := by
    simp only [w, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  rw [hsplit, hz1, hz2]
  simp only [Finset.sum_ite_eq', Finset.mem_range, show N < N + 1 + (N + 1) by omega,
    show N + 1 < N + 1 + (N + 1) by omega, if_true]
  have h := harm N
  have h2 := mul_le_mul_of_nonneg_left
    (show ∑ k ∈ Finset.range (N + 1), 1 / (k : ℝ) + ∑ k ∈ Finset.range (N + 1), 1 / (k : ℝ)
      ≤ 2 * (1 + Real.log N) by linarith) hB
  linarith

/- English proof (translation)
Establish `h1` using `Real.log_two_gt_d9`. Establish `h2 : Real.log 2 ≤ Real.log u` using `Real.log_le_log (by norm_num) hu`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma half_le_log {u : ℝ} (hu : 2 ≤ u) : 1 / 2 ≤ Real.log u := by
  have h1 := Real.log_two_gt_d9
  have h2 : Real.log 2 ≤ Real.log u := Real.log_le_log (by norm_num) hu
  linarith

/- English proof (translation)
Establish `hu0 : 0 < u` using `by linarith`. Establish `hn0 : (0 : ℝ) < n` using `by exact_mod_cast hn`. Establish `hL` using `half_le_log hu`. Use `set L := Real.log u with hLdef`. Establish `hL0 : 0 < L` using `by linarith`.

Use `set a := 1 / (2 * L) with ha`. Establish `hlogn : 0 ≤ Real.log n` using `Real.log_nonneg (by exact_mod_cast hn)`. Establish `habs : 1 / 2 ≤ |Real.log (u / n)|`. Break down `hf with hf | hf` into its components or cases. Establish `h2 : 2 ≤ u / n` using `by rw [le_div_iff₀ hn0]; linarith`.

Conclude with `(half_le_log h2).trans (le_abs_self _)`. Establish `h2 : 2 ≤ n / u` using `by rw [le_div_iff₀ hu0]; linarith`. Establish `h1` using `half_le_log h2`. Rewrite using `[Real.log_div hu0.ne' hn0.ne', abs_sub_comm, ← Real.log_div hn0.ne' hu0.ne']`. Conclude with `h1.trans (le_abs_self _)`.

Establish `key1 : E * T ≤ 2 * (C * (u / n) ^ (1 + 1 / L))`. Establish `h1 : E * (T * (1 / 2)) ≤ E * (T * |Real.log (u / n)|)` using `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left habs hT.le) hE`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hQ : 0 < (n : ℝ) ^ a` using `Real.rpow_pos_of_pos hn0 a`. Establish `hP : 0 < (n : ℝ) ^ (1 + a)` using `Real.rpow_pos_of_pos hn0 _`.

Establish `hexp : 1 + a + a = 1 + 1 / L` using `by rw [ha]; ring`. Establish `key2 : (u / n) ^ (1 + 1 / L) * ((n : ℝ) ^ (1 + a) * (n : ℝ) ^ a) = u * Real.exp 1`. Rewrite using `[← Real.rpow_add hn0, hexp, Real.div_rpow hu0.le hn0.le, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hn0 _).ne', Real.rpow_add hu0, Real.rpow_one, Real.rpow_def_of_pos hu0, ← hLdef, mul_one_div_cancel hL0.ne']`. Establish `key3 : Real.log n ≤ 2 * L * (n : ℝ) ^ a`. Establish `h1` using `Real.log_le_sub_one_of_pos hQ`.

Rewrite `h1` using `[Real.log_rpow hn0]`. Establish `h2 : 2 * L * a = 1` using `by rw [ha]; field_simp`. Combine the equalities or inequalities in the displayed calculation. Establish `he : Real.exp 1 < 3` using `by have := Real.exp_one_lt_d9; linarith`. Establish `hgoal : C * (12 * u * L / T * (1 / (n : ℝ) ^ (1 + a))) = (12 * C * u * L) / (T * (n : ℝ) ^ (1 + a))`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hgoal, le_div_iff₀ (mul_pos hT hP)]`. Establish `h0 : 0 ≤ C * L * u` using `mul_nonneg (mul_nonneg hC hL0.le) hu0.le`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_right _ hP.le` to reduce the goal to its premises.

Conclude with `mul_le_mul key3 key1 (mul_nonneg hE hT.le) (mul_nonneg (by linarith) hQ.le)`. Use `_ = 4 * C * L * ((u / n) ^ (1 + 1 / L) * ((n : ℝ) ^ (1 + a) * (n : ℝ) ^ a)) := by ring`. Use `_ = 4 * C * L * (u * Real.exp 1) := by rw [key2]`. Use `_ ≤ 12 * C * u * L := by nlinarith`.
-/
lemma far_term {u T C E : ℝ} {n : ℕ} (hu : 2 ≤ u) (hT : 0 < T) (hn : 0 < n) (hC : 0 ≤ C)
    (hE : 0 ≤ E) (h : E * (T * |Real.log (u / n)|) ≤ C * (u / n) ^ (1 + 1 / Real.log u))
    (hf : (n : ℝ) ≤ u / 2 ∨ 2 * u ≤ n) :
    Real.log n * E ≤ C * (12 * u * Real.log u / T
      * (1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log u)))) := by
  have hu0 : 0 < u := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL := half_le_log hu
  set L := Real.log u with hLdef
  have hL0 : 0 < L := by linarith
  set a := 1 / (2 * L) with ha
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have habs : 1 / 2 ≤ |Real.log (u / n)| := by
    rcases hf with hf | hf
    · have h2 : 2 ≤ u / n := by rw [le_div_iff₀ hn0]; linarith
      exact (half_le_log h2).trans (le_abs_self _)
    · have h2 : 2 ≤ n / u := by rw [le_div_iff₀ hu0]; linarith
      have h1 := half_le_log h2
      rw [Real.log_div hu0.ne' hn0.ne', abs_sub_comm, ← Real.log_div hn0.ne' hu0.ne']
      exact h1.trans (le_abs_self _)
  have key1 : E * T ≤ 2 * (C * (u / n) ^ (1 + 1 / L)) := by
    have h1 : E * (T * (1 / 2)) ≤ E * (T * |Real.log (u / n)|) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left habs hT.le) hE
    linarith
  have hQ : 0 < (n : ℝ) ^ a := Real.rpow_pos_of_pos hn0 a
  have hP : 0 < (n : ℝ) ^ (1 + a) := Real.rpow_pos_of_pos hn0 _
  have hexp : 1 + a + a = 1 + 1 / L := by rw [ha]; ring
  have key2 : (u / n) ^ (1 + 1 / L) * ((n : ℝ) ^ (1 + a) * (n : ℝ) ^ a) = u * Real.exp 1 := by
    rw [← Real.rpow_add hn0, hexp, Real.div_rpow hu0.le hn0.le,
      div_mul_cancel₀ _ (Real.rpow_pos_of_pos hn0 _).ne', Real.rpow_add hu0, Real.rpow_one,
      Real.rpow_def_of_pos hu0, ← hLdef, mul_one_div_cancel hL0.ne']
  have key3 : Real.log n ≤ 2 * L * (n : ℝ) ^ a := by
    have h1 := Real.log_le_sub_one_of_pos hQ
    rw [Real.log_rpow hn0] at h1
    have h2 : 2 * L * a = 1 := by rw [ha]; field_simp
    calc Real.log n = 2 * L * (a * Real.log n) := by rw [← mul_assoc, h2, one_mul]
      _ ≤ 2 * L * ((n : ℝ) ^ a - 1) := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ ≤ 2 * L * (n : ℝ) ^ a := by nlinarith
  have he : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
  have hgoal : C * (12 * u * L / T * (1 / (n : ℝ) ^ (1 + a)))
      = (12 * C * u * L) / (T * (n : ℝ) ^ (1 + a)) := by
    field_simp
  rw [hgoal, le_div_iff₀ (mul_pos hT hP)]
  have h0 : 0 ≤ C * L * u := mul_nonneg (mul_nonneg hC hL0.le) hu0.le
  calc Real.log n * E * (T * (n : ℝ) ^ (1 + a)) = Real.log n * (E * T) * (n : ℝ) ^ (1 + a) := by ring
    _ ≤ (2 * L * (n : ℝ) ^ a) * (2 * (C * (u / n) ^ (1 + 1 / L))) * (n : ℝ) ^ (1 + a) := by
        apply mul_le_mul_of_nonneg_right _ hP.le
        exact mul_le_mul key3 key1 (mul_nonneg hE hT.le) (mul_nonneg (by linarith) hQ.le)
    _ = 4 * C * L * ((u / n) ^ (1 + 1 / L) * ((n : ℝ) ^ (1 + a) * (n : ℝ) ^ a)) := by ring
    _ = 4 * C * L * (u * Real.exp 1) := by rw [key2]
    _ ≤ 12 * C * u * L := by nlinarith

/- English proof (translation)
Establish `hu0 : 0 < u` using `by linarith`. Establish `hL` using `half_le_log hu`. Use `set L := Real.log u with hLdef`. Establish `hL0 : 0 < L` using `by linarith`. Use `set N := ⌊u⌋₊ with hN`.

Use `set B := 2 * u / T with hB`. Establish `hB0 : 0 ≤ B` using `div_nonneg (by linarith) hT.le`. Establish `hn1 : (1 : ℝ) < n` using `by linarith`. Establish `hn0 : (0 : ℝ) < n` using `by linarith`. Establish `hlogn0 : 0 ≤ Real.log n` using `Real.log_nonneg hn1.le`.

Establish `hlog2 : Real.log 2 ≤ L` using `Real.log_le_log (by norm_num) hu`. Establish `hlogn : Real.log n ≤ 2 * L`. Establish `h2 : Real.log n ≤ Real.log (2 * u)` using `Real.log_le_log hn0 hf2.le`. Rewrite `h2` using `[Real.log_mul (by norm_num) hu0.ne']`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hM : (u / n) ^ (1 + 1 / L) ≤ 6`. Establish `hr : u / n ≤ 2` using `by rw [div_le_iff₀ hn0]; linarith`. Establish `hσ : 0 ≤ 1 + 1 / L` using `by have := one_div_pos.2 hL0; linarith`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.rpow_add (by norm_num), Real.rpow_one, Real.rpow_def_of_pos (by norm_num)]`.

Use `_ ≤ 2 * Real.exp 1 := by gcongr`. Rewrite using `[mul_one_div, div_le_one hL0]`. Conclude with `hlog2`. Use `_ ≤ 6 := by have := Real.exp_one_lt_d9; linarith`. Establish `hCM : C * (u / n) ^ (1 + 1 / L) ≤ 6 * C`.

Use `mul_le_mul_of_nonneg_left hM hC` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hCL : 0 ≤ C * L` using `mul_nonneg hC hL0.le`. Establish `hwdef : w N B n = (if n = N then 1 else 0) + (if n = N + 1 then 1 else 0) + B * (1 / ((N - n : ℕ) : ℝ) + 1 / ((n - (N + 1) : ℕ) : ℝ))` using `rfl`. Establish `hrest : 0 ≤ B * (1 / ((N - n : ℕ) : ℝ) + 1 / ((n - (N + 1) : ℕ) : ℝ))` using `mul_nonneg hB0 (by positivity)`.

Establish `caseA : 1 ≤ w N B n → Real.log n * E ≤ C * (16 * L * w N B n)`. Introduce `hw1`. Establish `h1 : Real.log n * E ≤ 2 * L * (6 * C)` using `mul_le_mul hlogn (h0.trans hCM) hE (by linarith)`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hw1 hCL]`. Establish `core : ∀ k : ℝ, 0 < k → k / (2 * u) ≤ |Real.log (u / n)| → B * (1 / k) ≤ w N B n → Real.log n * E ≤ C * (16 * L * w N B n)`.

Introduce `k hk hlog hwk`. Establish `h1 : E * (T * (k / (2 * u))) ≤ 6 * C` using `le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog hT.le) hE) (h.trans hCM)`. Establish `h2 : E * k = E * (T * (k / (2 * u))) * B`. Rewrite using `[hB]`. Clear the denominators using the available nonvanishing facts.

Establish `h3 : E * k ≤ 6 * C * B`. Rewrite using `[h2]`. Conclude with `mul_le_mul_of_nonneg_right h1 hB0`. Establish `h4 : Real.log n * E * k ≤ 2 * L * (6 * C * B)`. Rewrite using `[mul_assoc]`.

Conclude with `mul_le_mul hlogn h3 (mul_nonneg hE hk.le) (by linarith)`. Establish `h5 : Real.log n * E ≤ 12 * C * L * (B * (1 / k))`. Rewrite using `[show 12 * C * L * (B * (1 / k)) = (12 * C * L * B) / k by ring, le_div_iff₀ hk]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbk : 0 ≤ B * (1 / k)` using `mul_nonneg hB0 (by positivity)`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hwk hCL, mul_nonneg hCL hbk]`. Establish `hNu : (N : ℝ) ≤ u` using `Nat.floor_le hu0.le`. Establish `huN : u < (N : ℝ) + 1` using `Nat.lt_floor_add_one u`. Break down `lt_trichotomy n N with hlt | heq | hgt` into its components or cases. Establish `hlt' : (n : ℝ) < N` using `by exact_mod_cast hlt`.

Establish `hk : (0 : ℝ) < (N : ℝ) - n` using `sub_pos.2 hlt'`. Apply `core ((N : ℝ) - n) hk` to reduce the goal to its premises. Establish `h1` using `Real.one_sub_inv_le_log_of_pos (div_pos hu0 hn0)`. Rewrite `h1` using `[inv_div]`. Establish `e1 : 1 - n / u = (u - n) / u` using `by field_simp`.

Establish `e2 : ((N : ℝ) - n) / (2 * u) ≤ (u - n) / (2 * u)` using `div_le_div_of_nonneg_right (by linarith) (by linarith)`. Establish `e3 : (u - n) / (2 * u) ≤ (u - n) / u` using `div_le_div_of_nonneg_left (by linarith) hu0 (by linarith)`. Rewrite `h1` using `[e1]`. Conclude with `e2.trans (e3.trans (h1.trans (le_abs_self _)))`. Establish `hcast : ((N - n : ℕ) : ℝ) = (N : ℝ) - n` using `Nat.cast_sub hlt.le`.

Rewrite using `[hwdef, hcast, if_neg hlt.ne, if_neg (by omega), mul_add]`. Establish `: 0 ≤ B * (1 / ((n - (N + 1) : ℕ) : ℝ))` using `mul_nonneg hB0 (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Apply `caseA` to reduce the goal to its premises. Rewrite using `[hwdef, if_pos heq]`.

Apply the tactic sequence `have : (0 : ℝ) ≤ if n = N + 1 then 1 else 0 := by split_ifs <;> norm_num`. Combine the linear equalities and inequalities to obtain the conclusion. Break down `Nat.lt_or_ge (N + 1) n with hgt2 | hle` into its components or cases. Establish `hgt2' : (N : ℝ) + 1 < n` using `by exact_mod_cast hgt2`. Establish `hk : (0 : ℝ) < (n : ℝ) - (N + 1)` using `by linarith`.

Apply `core ((n : ℝ) - (N + 1)) hk` to reduce the goal to its premises. Establish `h1` using `Real.one_sub_inv_le_log_of_pos (div_pos hn0 hu0)`. Rewrite `h1` using `[inv_div]`. Establish `e1 : 1 - u / n = (n - u) / n` using `by field_simp`. Establish `e2 : ((n : ℝ) - (N + 1)) / (2 * u) ≤ (n - u) / (2 * u)` using `div_le_div_of_nonneg_right (by linarith) (by linarith)`.

Establish `e3 : ((n : ℝ) - u) / (2 * u) ≤ (n - u) / n` using `div_le_div_of_nonneg_left (by linarith) hn0 hf2.le`. Rewrite `h1` using `[e1]`. Establish `habs : Real.log (n / u) ≤ |Real.log (u / n)|`. Rewrite using `[Real.log_div hu0.ne' hn0.ne', abs_sub_comm, ← Real.log_div hn0.ne' hu0.ne']`. Conclude with `le_abs_self _`.

Conclude with `e2.trans (e3.trans (h1.trans habs))`. Establish `hcast : ((n - (N + 1) : ℕ) : ℝ) = (n : ℝ) - (N + 1)`. Rewrite using `[Nat.cast_sub hgt2.le]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hwdef, hcast, if_neg (by omega), if_neg (by omega), mul_add]`. Establish `: 0 ≤ B * (1 / ((N - n : ℕ) : ℝ))` using `mul_nonneg hB0 (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `heq1 : n = N + 1` using `by omega`. Apply `caseA` to reduce the goal to its premises.

Rewrite using `[hwdef, if_neg (by omega), if_pos heq1]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma near_term {u T C E : ℝ} {n : ℕ} (hu : 2 ≤ u) (hT : 0 < T) (hC : 0 ≤ C)
    (hE : 0 ≤ E) (h0 : E ≤ C * (u / n) ^ (1 + 1 / Real.log u))
    (h : E * (T * |Real.log (u / n)|) ≤ C * (u / n) ^ (1 + 1 / Real.log u))
    (hf1 : u / 2 < n) (hf2 : n < 2 * u) :
    Real.log n * E ≤ C * (16 * Real.log u * w ⌊u⌋₊ (2 * u / T) n) := by
  have hu0 : 0 < u := by linarith
  have hL := half_le_log hu
  set L := Real.log u with hLdef
  have hL0 : 0 < L := by linarith
  set N := ⌊u⌋₊ with hN
  set B := 2 * u / T with hB
  have hB0 : 0 ≤ B := div_nonneg (by linarith) hT.le
  have hn1 : (1 : ℝ) < n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1.le
  have hlog2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hu
  have hlogn : Real.log n ≤ 2 * L := by
    have h2 : Real.log n ≤ Real.log (2 * u) := Real.log_le_log hn0 hf2.le
    rw [Real.log_mul (by norm_num) hu0.ne'] at h2
    linarith
  have hM : (u / n) ^ (1 + 1 / L) ≤ 6 := by
    have hr : u / n ≤ 2 := by rw [div_le_iff₀ hn0]; linarith
    have hσ : 0 ≤ 1 + 1 / L := by have := one_div_pos.2 hL0; linarith
    calc (u / n) ^ (1 + 1 / L) ≤ (2 : ℝ) ^ (1 + 1 / L) :=
          Real.rpow_le_rpow (div_nonneg hu0.le hn0.le) hr hσ
      _ = 2 * Real.exp (Real.log 2 * (1 / L)) := by
          rw [Real.rpow_add (by norm_num), Real.rpow_one, Real.rpow_def_of_pos (by norm_num)]
      _ ≤ 2 * Real.exp 1 := by
          gcongr
          rw [mul_one_div, div_le_one hL0]
          exact hlog2
      _ ≤ 6 := by have := Real.exp_one_lt_d9; linarith
  have hCM : C * (u / n) ^ (1 + 1 / L) ≤ 6 * C := by
    have := mul_le_mul_of_nonneg_left hM hC
    linarith
  have hCL : 0 ≤ C * L := mul_nonneg hC hL0.le
  have hwdef : w N B n = (if n = N then 1 else 0) + (if n = N + 1 then 1 else 0)
      + B * (1 / ((N - n : ℕ) : ℝ) + 1 / ((n - (N + 1) : ℕ) : ℝ)) := rfl
  have hrest : 0 ≤ B * (1 / ((N - n : ℕ) : ℝ) + 1 / ((n - (N + 1) : ℕ) : ℝ)) :=
    mul_nonneg hB0 (by positivity)
  have caseA : 1 ≤ w N B n → Real.log n * E ≤ C * (16 * L * w N B n) := by
    intro hw1
    have h1 : Real.log n * E ≤ 2 * L * (6 * C) :=
      mul_le_mul hlogn (h0.trans hCM) hE (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hw1 hCL]
  have core : ∀ k : ℝ, 0 < k → k / (2 * u) ≤ |Real.log (u / n)| → B * (1 / k) ≤ w N B n →
      Real.log n * E ≤ C * (16 * L * w N B n) := by
    intro k hk hlog hwk
    have h1 : E * (T * (k / (2 * u))) ≤ 6 * C :=
      le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog hT.le) hE) (h.trans hCM)
    have h2 : E * k = E * (T * (k / (2 * u))) * B := by
      rw [hB]
      field_simp
    have h3 : E * k ≤ 6 * C * B := by
      rw [h2]
      exact mul_le_mul_of_nonneg_right h1 hB0
    have h4 : Real.log n * E * k ≤ 2 * L * (6 * C * B) := by
      rw [mul_assoc]
      exact mul_le_mul hlogn h3 (mul_nonneg hE hk.le) (by linarith)
    have h5 : Real.log n * E ≤ 12 * C * L * (B * (1 / k)) := by
      rw [show 12 * C * L * (B * (1 / k)) = (12 * C * L * B) / k by ring, le_div_iff₀ hk]
      linarith
    have hbk : 0 ≤ B * (1 / k) := mul_nonneg hB0 (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hwk hCL, mul_nonneg hCL hbk]
  have hNu : (N : ℝ) ≤ u := Nat.floor_le hu0.le
  have huN : u < (N : ℝ) + 1 := Nat.lt_floor_add_one u
  rcases lt_trichotomy n N with hlt | heq | hgt
  · have hlt' : (n : ℝ) < N := by exact_mod_cast hlt
    have hk : (0 : ℝ) < (N : ℝ) - n := sub_pos.2 hlt'
    apply core ((N : ℝ) - n) hk
    · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hu0 hn0)
      rw [inv_div] at h1
      have e1 : 1 - n / u = (u - n) / u := by field_simp
      have e2 : ((N : ℝ) - n) / (2 * u) ≤ (u - n) / (2 * u) :=
        div_le_div_of_nonneg_right (by linarith) (by linarith)
      have e3 : (u - n) / (2 * u) ≤ (u - n) / u :=
        div_le_div_of_nonneg_left (by linarith) hu0 (by linarith)
      rw [e1] at h1
      exact e2.trans (e3.trans (h1.trans (le_abs_self _)))
    · have hcast : ((N - n : ℕ) : ℝ) = (N : ℝ) - n := Nat.cast_sub hlt.le
      rw [hwdef, hcast, if_neg hlt.ne, if_neg (by omega), mul_add]
      have : 0 ≤ B * (1 / ((n - (N + 1) : ℕ) : ℝ)) := mul_nonneg hB0 (by positivity)
      linarith
  · apply caseA
    rw [hwdef, if_pos heq]
    have : (0 : ℝ) ≤ if n = N + 1 then 1 else 0 := by split_ifs <;> norm_num
    linarith
  · rcases Nat.lt_or_ge (N + 1) n with hgt2 | hle
    · have hgt2' : (N : ℝ) + 1 < n := by exact_mod_cast hgt2
      have hk : (0 : ℝ) < (n : ℝ) - (N + 1) := by linarith
      apply core ((n : ℝ) - (N + 1)) hk
      · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hn0 hu0)
        rw [inv_div] at h1
        have e1 : 1 - u / n = (n - u) / n := by field_simp
        have e2 : ((n : ℝ) - (N + 1)) / (2 * u) ≤ (n - u) / (2 * u) :=
          div_le_div_of_nonneg_right (by linarith) (by linarith)
        have e3 : ((n : ℝ) - u) / (2 * u) ≤ (n - u) / n :=
          div_le_div_of_nonneg_left (by linarith) hn0 hf2.le
        rw [e1] at h1
        have habs : Real.log (n / u) ≤ |Real.log (u / n)| := by
          rw [Real.log_div hu0.ne' hn0.ne', abs_sub_comm, ← Real.log_div hn0.ne' hu0.ne']
          exact le_abs_self _
        exact e2.trans (e3.trans (h1.trans habs))
      · have hcast : ((n - (N + 1) : ℕ) : ℝ) = (n : ℝ) - (N + 1) := by
          rw [Nat.cast_sub hgt2.le]
          push_cast
          ring
        rw [hwdef, hcast, if_neg (by omega), if_neg (by omega), mul_add]
        have : 0 ≤ B * (1 / ((N - n : ℕ) : ℝ)) := mul_nonneg hB0 (by positivity)
        linarith
    · have heq1 : n = N + 1 := by omega
      apply caseA
      rw [hwdef, if_neg (by omega), if_pos heq1]
      linarith

/- English proof (translation)
Take `⟨C0, hC0, hK⟩` from `kernel_bound`. Use `⟨240 * C0, by positivity, ?_⟩` and prove the remaining obligations. Introduce `q _ χ u T hT2 hTu hu`. Establish `hu0 : 0 < u` using `by linarith`. Establish `hT0 : 0 < T` using `by linarith`.

Establish `hL` using `half_le_log hu`. Use `set L := Real.log u with hLdef`. Establish `hL0 : 0 < L` using `by linarith`. Use `set σ : ℝ := 1 + 1 / L with hσ`. Establish `hσ1 : 1 < σ`.

Use `one_div_pos.2 hL0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `set N := ⌊u⌋₊ with hN`. Use `set B := 2 * u / T with hB`. Establish `hB0 : 0 ≤ B` using `div_nonneg (by linarith) hT0.le`.

Use `set a : ℕ → ℂ := fun n => (Λ n : ℂ) * χ (n : ZMod q) with ha`. Establish `ha0 : a 0 = 0` using `by simp [ha]`. Establish `hre : ∀ t : ℝ, 1 < ((σ : ℂ) + t * I).re` using `fun t => by simpa using hσ1`. Establish `hsum : LSeriesSummable a σ`. Establish `h1` using `LSeriesSummable_twist_vonMangoldt χ (s := (σ : ℂ)) (by simpa using hσ1)`.

Use `h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `n`. Simplify using `only [ha, Pi.mul_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hLS : ∀ t : ℝ, -(deriv (LFunction χ) ((σ : ℂ) + t * I) / LFunction χ ((σ : ℂ) + t * I)) = LSeries a ((σ : ℂ) + t * I)`.

Introduce `t`. Rewrite using `[LFunction_eq_LSeries χ (hre t), deriv_LFunction_eq_deriv_LSeries χ (hre t), ← neg_div, ← LSeries_twist_vonMangoldt_eq χ (hre t)]`. Use `congr 1`. Use function extensionality and compare the values at `n`. Simplify using `only [ha, Pi.mul_apply]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hJ : ∫ t in (-T)..T, -(deriv (LFunction χ) ((σ : ℂ) + t * I) / LFunction χ ((σ : ℂ) + t * I)) * (u : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I) = ∫ t in (-T)..T, LSeries a ((σ : ℂ) + t * I) * (u : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)`. Apply `intervalIntegral.integral_congr` to reduce the goal to its premises. Introduce `t _`. Simplify using `only`.

Rewrite using `[hLS t]`. Establish `hI` using `interchange a ha0 T (one_pos.trans hσ1) hu0 hsum`. Establish `hfin : HasSum (fun n => a n * (if 1 ≤ u / n then (1 : ℂ) else 0)) (∑ n ∈ Finset.Icc 1 N, a n)`. Establish `h : HasSum (fun n => a n * (if 1 ≤ u / n then (1 : ℂ) else 0)) (∑ n ∈ Finset.Icc 1 N, a n * (if 1 ≤ u / n then (1 : ℂ) else 0))` using `hasSum_sum_of_ne_finset_zero (by`. Introduce `n hn`.

Distinguish the cases in `h0 : n = 0`. Simplify using `[h0, ha0]`. Establish `hnN : N < n`. Rewrite `hn` using `[Finset.mem_Icc]`. Use linear arithmetic over natural numbers and integers.

Establish `hlt : u < n` using `(Nat.floor_lt hu0.le).1 hnN`. Establish `hnpos : (0 : ℝ) < n` using `by exact_mod_cast Nat.pos_of_ne_zero h0`. Establish `hnot : ¬ (1 ≤ u / n)`. Rewrite using `[not_le, div_lt_one hnpos]`. Conclude with `hlt`.

Simplify using `[hnot])`. Use `h using 1` and compare the differences between its conclusion and the goal. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `n hn`. Rewrite `hn` using `[Finset.mem_Icc]`.

Establish `hnpos : (0 : ℝ) < n` using `by exact_mod_cast (show 0 < n by omega)`. Establish `hle : (n : ℝ) ≤ u` using `(Nat.le_floor_iff hu0.le).1 hn.2`. Establish `h1 : 1 ≤ u / n` using `by rw [le_div_iff₀ hnpos]; linarith`. Simplify using `[h1]`. Establish `hcomb` using `hfin.sub (hI.mul_left (1 / (2 * Real.pi) : ℂ))`.

Establish `hτ1 : 1 < 1 + 1 / (2 * L)`. Use `one_div_pos.2 (show 0 < 2 * L by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs1 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 + 1 / (2 * L)))` using `Real.summable_one_div_nat_rpow.2 hτ1`. Establish `hA : 0 ≤ 12 * u * L / T` using `div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hu0.le) hL0.le) hT0.le`.

Establish `hW0 : ∀ n, 0 ≤ (if n ∈ Finset.range (N + 1 + (N + 1)) then w N B n else 0)`. Introduce `n`. Use `split_ifs`. Conclude with `w_nonneg N hB0 n`. Conclude with `le_rfl`.

Establish `hg : HasSum (fun n : ℕ => C0 * (12 * u * L / T * (1 / (n : ℝ) ^ (1 + 1 / (2 * L)))) + C0 * (16 * L * (if n ∈ Finset.range (N + 1 + (N + 1)) then w N B n else 0))) (C0 * (12 * u * L / T * ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / (2 * L))) + C0 * (16 * L * ∑ n ∈ Finset.range (N + 1 + (N + …`. Use `HasSum.add ((hs1.hasSum.mul_left _).mul_left _) ((HasSum.mul_left _ ?_).mul_left _)` and prove the remaining obligations. Conclude with `hasSum_sum_of_ne_finset_zero (fun n hn => if_neg hn)`. Establish `hpt : ∀ n : ℕ, ‖a n * (if 1 ≤ u / n then (1 : ℂ) else 0) - (1 / (2 * Real.pi) : ℂ) * (a n * ∫ t in (-T)..T, ((u / n : ℝ) : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I))‖ ≤ C0 * (12 * u * L / T * (1 / (n : ℝ) ^ (1 + 1 / (2 * L)))) + C0 * (16 * L * (if n ∈ Finset.range (N + 1 + (N + …`. Introduce `n`.

Establish `hg1 : 0 ≤ C0 * (12 * u * L / T * (1 / (n : ℝ) ^ (1 + 1 / (2 * L))))` using `mul_nonneg hC0.le (mul_nonneg hA (by positivity))`. Establish `hg2 : 0 ≤ C0 * (16 * L * (if n ∈ Finset.range (N + 1 + (N + 1)) then w N B n else 0))` using `mul_nonneg hC0.le (mul_nonneg (by linarith) (hW0 n))`. Distinguish the cases in `h0 : n = 0`. Substitute `h0` using the available equality. Rewrite using `[ha0]`.

Simplify using `only [zero_mul, mul_zero, sub_zero, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn0 : (0 : ℝ) < n` using `by exact_mod_cast Nat.pos_of_ne_zero h0`. Establish `e : a n * (if 1 ≤ u / n then (1 : ℂ) else 0) - (1 / (2 * Real.pi) : ℂ) * (a n * ∫ t in (-T)..T, ((u / n : ℝ) : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)) = -(a n * ((1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T, ((u / n : ℝ) : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)) - (if 1 ≤ u …` using `by ring`. Rewrite using `[e, norm_neg, norm_mul]`.

Establish `han : ‖a n‖ ≤ Real.log n` using `by show ‖(Λ n : ℂ) * χ (n : ZMod q)‖ ≤ Real.log n`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨hk1, hk2⟩` from `hK (u / n) σ T (div_pos hu0 hn0) (one_pos.trans hσ1) (by linarith)`. Establish `hstep` using `mul_le_mul_of_nonneg_right han (norm_nonneg ((1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T, ((u / n : ℝ) : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)) - (if 1 ≤ u / n then (1 : ℂ) else 0)))`.

Distinguish the cases in `hfar : (n : ℝ) ≤ u / 2 ∨ 2 * u ≤ n`. Establish `hft` using `far_term hu hT0 (Nat.pos_of_ne_zero h0) hC0.le (norm_nonneg _) hk2 hfar`. Combine the linear equalities and inequalities to obtain the conclusion. Use `push Not at hfar`. Take `⟨h1, h2⟩` from `hfar`.

Establish `hnt` using `near_term hu hT0 hC0.le (norm_nonneg _) hk1 hk2 h1 h2`. Establish `hmem : n ∈ Finset.range (N + 1 + (N + 1))`. Establish `huN : u < (N : ℝ) + 1` using `Nat.lt_floor_add_one u`. Establish `h3 : (n : ℝ) < ((N + 1 + (N + 1) : ℕ) : ℝ)`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Finset.mem_range]`. Conclude with `h3` after adjusting the coercions. Rewrite using `[if_pos hmem]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `key` using `hcomb.norm_le_of_bounded hg hpt`. Establish `hZ : ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / (2 * L)) ≤ 1 + 2 * L`. Establish `h1` using `zeta_bound hτ1`. Rewrite `h1` using `[add_sub_cancel_left, one_div_one_div]`. Then use the resulting hypothesis. Establish `hWeq : ∑ n ∈ Finset.range (N + 1 + (N + 1)), (if n ∈ Finset.range (N + 1 + (N + 1)) then w N B n else 0) = ∑ n ∈ Finset.range (N + 1 + (N + 1)), w N B n` using `Finset.sum_congr rfl (fun n hn => if_pos hn)`.

Establish `hlogN : Real.log N ≤ L`. Establish `h2 : (2 : ℕ) ≤ N` using `Nat.le_floor (by exact_mod_cast hu)`. Establish `hNpos : (0 : ℝ) < N` using `by exact_mod_cast (show 0 < N by omega)`. Conclude with `Real.log_le_log hNpos (Nat.floor_le hu0.le)`. Establish `hW : ∑ n ∈ Finset.range (N + 1 + (N + 1)), w N B n ≤ 2 + B * (2 * (1 + L))`.

Establish `h1` using `sum_w N hB0`. Establish `h2 : B * (2 * (1 + Real.log N)) ≤ B * (2 * (1 + L))` using `mul_le_mul_of_nonneg_left (by linarith) hB0`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hJ]`. Use `key.trans ?_` and prove the remaining obligations.

Rewrite using `[hWeq]`. Establish `hX : 0 < u / T` using `div_pos hu0 hT0`. Establish `e1 : 12 * u * L / T = 12 * L * (u / T)` using `by ring`. Establish `e2 : B = 2 * (u / T)` using `by rw [hB]; ring`. Establish `e3 : u * L ^ 2 / T = L ^ 2 * (u / T)` using `by ring`.

Establish `b1` using `mul_le_mul_of_nonneg_left hZ hA`. Establish `b2` using `mul_le_mul_of_nonneg_left hW (show (0 : ℝ) ≤ 16 * L by linarith)`. Establish `b3 : 12 * u * L / T * (1 + 2 * L) + 16 * L * (2 + B * (2 * (1 + L))) ≤ 240 * (u * L ^ 2 / T + L)`. Rewrite using `[e1, e2, e3]`. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg hL0.le hX.le) (show (0 : ℝ) ≤ 2 * L - 1 by linarith), mul_nonneg (mul_nonneg hL0.le hL0.le) hX.le]`.

Establish `b4 : 12 * u * L / T * ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / (2 * L)) + 16 * L * ∑ n ∈ Finset.range (N + 1 + (N + 1)), w N B n ≤ 240 * (u * L ^ 2 / T + L)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `b5` using `mul_le_mul_of_nonneg_left b4 hC0.le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem truncated_perron_psi : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (u T : ℝ), 2 ≤ T → T ≤ 2 * u → 2 ≤ u → ‖(∑ n ∈ Finset.Icc 1 ⌊u⌋₊, (Λ n : ℂ) * χ (n : ZMod q)) - (1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T, -(deriv (LFunction χ) ((1 + 1 / Real.log u : ℝ) + t * I) / LFunction χ ((1 + 1 / Real.log u : ℝ) + t * I)) * (u : ℂ) ^ (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) / ((1 + 1 / Real.log u : ℝ) + t * I)‖ ≤ C * (u * Real.log u ^ 2 / T + Real.log u) := by
  obtain ⟨C0, hC0, hK⟩ := kernel_bound
  refine ⟨240 * C0, by positivity, ?_⟩
  intro q _ χ u T hT2 hTu hu
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hL := half_le_log hu
  set L := Real.log u with hLdef
  have hL0 : 0 < L := by linarith
  set σ : ℝ := 1 + 1 / L with hσ
  have hσ1 : 1 < σ := by
    have := one_div_pos.2 hL0
    linarith
  set N := ⌊u⌋₊ with hN
  set B := 2 * u / T with hB
  have hB0 : 0 ≤ B := div_nonneg (by linarith) hT0.le
  set a : ℕ → ℂ := fun n => (Λ n : ℂ) * χ (n : ZMod q) with ha
  have ha0 : a 0 = 0 := by simp [ha]
  have hre : ∀ t : ℝ, 1 < ((σ : ℂ) + t * I).re := fun t => by simpa using hσ1
  have hsum : LSeriesSummable a σ := by
    have h1 := LSeriesSummable_twist_vonMangoldt χ (s := (σ : ℂ)) (by simpa using hσ1)
    convert h1 using 1
    funext n
    simp only [ha, Pi.mul_apply]
    ring
  have hLS : ∀ t : ℝ, -(deriv (LFunction χ) ((σ : ℂ) + t * I) / LFunction χ ((σ : ℂ) + t * I))
      = LSeries a ((σ : ℂ) + t * I) := by
    intro t
    rw [LFunction_eq_LSeries χ (hre t), deriv_LFunction_eq_deriv_LSeries χ (hre t), ← neg_div,
      ← LSeries_twist_vonMangoldt_eq χ (hre t)]
    congr 1
    funext n
    simp only [ha, Pi.mul_apply]
    ring
  have hJ : ∫ t in (-T)..T, -(deriv (LFunction χ) ((σ : ℂ) + t * I) / LFunction χ ((σ : ℂ) + t * I))
        * (u : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)
      = ∫ t in (-T)..T, LSeries a ((σ : ℂ) + t * I) * (u : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only
    rw [hLS t]
  have hI := interchange a ha0 T (one_pos.trans hσ1) hu0 hsum
  have hfin : HasSum (fun n => a n * (if 1 ≤ u / n then (1 : ℂ) else 0)) (∑ n ∈ Finset.Icc 1 N, a n) := by
    have h : HasSum (fun n => a n * (if 1 ≤ u / n then (1 : ℂ) else 0))
        (∑ n ∈ Finset.Icc 1 N, a n * (if 1 ≤ u / n then (1 : ℂ) else 0)) :=
      hasSum_sum_of_ne_finset_zero (by
        intro n hn
        by_cases h0 : n = 0
        · simp [h0, ha0]
        · have hnN : N < n := by
            rw [Finset.mem_Icc] at hn
            omega
          have hlt : u < n := (Nat.floor_lt hu0.le).1 hnN
          have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero h0
          have hnot : ¬ (1 ≤ u / n) := by
            rw [not_le, div_lt_one hnpos]
            exact hlt
          simp [hnot])
    convert h using 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hle : (n : ℝ) ≤ u := (Nat.le_floor_iff hu0.le).1 hn.2
    have h1 : 1 ≤ u / n := by rw [le_div_iff₀ hnpos]; linarith
    simp [h1]
  have hcomb := hfin.sub (hI.mul_left (1 / (2 * Real.pi) : ℂ))
  have hτ1 : 1 < 1 + 1 / (2 * L) := by
    have := one_div_pos.2 (show 0 < 2 * L by linarith)
    linarith
  have hs1 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 + 1 / (2 * L))) :=
    Real.summable_one_div_nat_rpow.2 hτ1
  have hA : 0 ≤ 12 * u * L / T :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hu0.le) hL0.le) hT0.le
  have hW0 : ∀ n, 0 ≤ (if n ∈ Finset.range (N + 1 + (N + 1)) then w N B n else 0) := by
    intro n
    split_ifs
    · exact w_nonneg N hB0 n
    · exact le_rfl
  have hg : HasSum (fun n : ℕ => C0 * (12 * u * L / T * (1 / (n : ℝ) ^ (1 + 1 / (2 * L))))
        + C0 * (16 * L * (if n ∈ Finset.range (N + 1 + (N + 1)) then w N B n else 0)))
      (C0 * (12 * u * L / T * ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / (2 * L)))
        + C0 * (16 * L * ∑ n ∈ Finset.range (N + 1 + (N + 1)),
          (if n ∈ Finset.range (N + 1 + (N + 1)) then w N B n else 0))) := by
    refine HasSum.add ((hs1.hasSum.mul_left _).mul_left _) ((HasSum.mul_left _ ?_).mul_left _)
    exact hasSum_sum_of_ne_finset_zero (fun n hn => if_neg hn)
  have hpt : ∀ n : ℕ, ‖a n * (if 1 ≤ u / n then (1 : ℂ) else 0)
      - (1 / (2 * Real.pi) : ℂ) * (a n * ∫ t in (-T)..T,
        ((u / n : ℝ) : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I))‖
      ≤ C0 * (12 * u * L / T * (1 / (n : ℝ) ^ (1 + 1 / (2 * L))))
        + C0 * (16 * L * (if n ∈ Finset.range (N + 1 + (N + 1)) then w N B n else 0)) := by
    intro n
    have hg1 : 0 ≤ C0 * (12 * u * L / T * (1 / (n : ℝ) ^ (1 + 1 / (2 * L)))) :=
      mul_nonneg hC0.le (mul_nonneg hA (by positivity))
    have hg2 : 0 ≤ C0 * (16 * L * (if n ∈ Finset.range (N + 1 + (N + 1)) then w N B n else 0)) :=
      mul_nonneg hC0.le (mul_nonneg (by linarith) (hW0 n))
    by_cases h0 : n = 0
    · subst h0
      rw [ha0]
      simp only [zero_mul, mul_zero, sub_zero, norm_zero]
      linarith
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero h0
    have e : a n * (if 1 ≤ u / n then (1 : ℂ) else 0)
        - (1 / (2 * Real.pi) : ℂ) * (a n * ∫ t in (-T)..T,
          ((u / n : ℝ) : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I))
        = -(a n * ((1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
          ((u / n : ℝ) : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I))
          - (if 1 ≤ u / n then (1 : ℂ) else 0))) := by ring
    rw [e, norm_neg, norm_mul]
    have han : ‖a n‖ ≤ Real.log n := by
      show ‖(Λ n : ℂ) * χ (n : ZMod q)‖ ≤ Real.log n
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
      calc Λ n * ‖χ (n : ZMod q)‖ ≤ Λ n * 1 :=
            mul_le_mul_of_nonneg_left (χ.norm_le_one _) vonMangoldt_nonneg
        _ ≤ Real.log n := by rw [mul_one]; exact vonMangoldt_le_log
    obtain ⟨hk1, hk2⟩ := hK (u / n) σ T (div_pos hu0 hn0) (one_pos.trans hσ1) (by linarith)
    have hstep := mul_le_mul_of_nonneg_right han (norm_nonneg
      ((1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
          ((u / n : ℝ) : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I))
          - (if 1 ≤ u / n then (1 : ℂ) else 0)))
    by_cases hfar : (n : ℝ) ≤ u / 2 ∨ 2 * u ≤ n
    · have hft := far_term hu hT0 (Nat.pos_of_ne_zero h0) hC0.le (norm_nonneg _) hk2 hfar
      linarith
    · push Not at hfar
      obtain ⟨h1, h2⟩ := hfar
      have hnt := near_term hu hT0 hC0.le (norm_nonneg _) hk1 hk2 h1 h2
      have hmem : n ∈ Finset.range (N + 1 + (N + 1)) := by
        have huN : u < (N : ℝ) + 1 := Nat.lt_floor_add_one u
        have h3 : (n : ℝ) < ((N + 1 + (N + 1) : ℕ) : ℝ) := by
          push_cast
          linarith
        rw [Finset.mem_range]
        exact_mod_cast h3
      rw [if_pos hmem]
      linarith
  have key := hcomb.norm_le_of_bounded hg hpt
  have hZ : ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / (2 * L)) ≤ 1 + 2 * L := by
    have h1 := zeta_bound hτ1
    rwa [add_sub_cancel_left, one_div_one_div] at h1
  have hWeq : ∑ n ∈ Finset.range (N + 1 + (N + 1)),
      (if n ∈ Finset.range (N + 1 + (N + 1)) then w N B n else 0)
      = ∑ n ∈ Finset.range (N + 1 + (N + 1)), w N B n :=
    Finset.sum_congr rfl (fun n hn => if_pos hn)
  have hlogN : Real.log N ≤ L := by
    have h2 : (2 : ℕ) ≤ N := Nat.le_floor (by exact_mod_cast hu)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    exact Real.log_le_log hNpos (Nat.floor_le hu0.le)
  have hW : ∑ n ∈ Finset.range (N + 1 + (N + 1)), w N B n ≤ 2 + B * (2 * (1 + L)) := by
    have h1 := sum_w N hB0
    have h2 : B * (2 * (1 + Real.log N)) ≤ B * (2 * (1 + L)) :=
      mul_le_mul_of_nonneg_left (by linarith) hB0
    linarith
  rw [hJ]
  refine key.trans ?_
  rw [hWeq]
  have hX : 0 < u / T := div_pos hu0 hT0
  have e1 : 12 * u * L / T = 12 * L * (u / T) := by ring
  have e2 : B = 2 * (u / T) := by rw [hB]; ring
  have e3 : u * L ^ 2 / T = L ^ 2 * (u / T) := by ring
  have b1 := mul_le_mul_of_nonneg_left hZ hA
  have b2 := mul_le_mul_of_nonneg_left hW (show (0 : ℝ) ≤ 16 * L by linarith)
  have b3 : 12 * u * L / T * (1 + 2 * L) + 16 * L * (2 + B * (2 * (1 + L)))
      ≤ 240 * (u * L ^ 2 / T + L) := by
    rw [e1, e2, e3]
    nlinarith [mul_nonneg (mul_nonneg hL0.le hX.le) (show (0 : ℝ) ≤ 2 * L - 1 by linarith),
      mul_nonneg (mul_nonneg hL0.le hL0.le) hX.le]
  have b4 : 12 * u * L / T * ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / (2 * L))
      + 16 * L * ∑ n ∈ Finset.range (N + 1 + (N + 1)), w N B n ≤ 240 * (u * L ^ 2 / T + L) := by
    linarith
  have b5 := mul_le_mul_of_nonneg_left b4 hC0.le
  linarith

end GlobalTheory.PerronPsi

import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.GoodHeightExists

namespace PI.EF.PK

open Complex MeasureTheory intervalIntegral Real ArithmeticFunction LSeries

/- English proof (translation)
Establish `h` using `Real.log_pos (by linarith : (1:ℝ) < u)`. Establish `h2` using `one_div_pos.mpr h`. Use `show 1 < 1 + 1 / Real.log u`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma one_lt_cLine {u : ℝ} (hu : 2 ≤ u) : 1 < cLine u := by
  have h := Real.log_pos (by linarith : (1:ℝ) < u)
  have h2 := one_div_pos.mpr h
  show 1 < 1 + 1 / Real.log u
  linarith

/- English proof (translation)
Take `⟨h1, h2⟩` from `hK y c T hy hc hT`. Distinguish the cases in `h : T * |Real.log y| ≤ 1`. Rewrite using `[kb, if_pos h]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `h` using `[kb, if_neg h] push_neg`.

Rewrite using `[mul_one_div, le_div_iff₀ (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma kernel_le_kb (hK : PerronKernel) (y c T : ℝ) (hy : 0 < y) (hc : 0 < c) (hT : 0 < T) :
    ‖perronK y c T - (if 1 ≤ y then 1 else 0)‖ ≤ y ^ c * kb T y := by
  obtain ⟨h1, h2⟩ := hK y c T hy hc hT
  by_cases h : T * |Real.log y| ≤ 1
  · rw [kb, if_pos h]
    linarith
  · rw [kb, if_neg h]
    push_neg at h
    rw [mul_one_div, le_div_iff₀ (by linarith)]
    linarith

/- English proof (translation)
Rewrite using `[LSeries.term_of_ne_zero hn, Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hu.le (Nat.cast_nonneg n)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma term_mul_kernel (a : ℕ → ℂ) (u : ℝ) (hu : 0 < u) (n : ℕ) (hn : n ≠ 0) (s : ℂ) :
    term a s n * ((u : ℂ) ^ s / s) = a n * (((u / n : ℝ) : ℂ) ^ s / s) := by
  rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg hu.le (Nat.cast_nonneg n)]
  push_cast
  ring

/- English proof (translation)
Introduce `a ha u T hu hT`. Establish `hc1 : 1 < cLine u` using `one_lt_cLine hu`. Use `set c := cLine u with hcdef`. Establish `hc0 : 0 < c` using `by linarith`. Establish `hu0 : 0 < u` using `by linarith`.

Establish `hT0 : 0 < T` using `by linarith`. Take `⟨hSs, hSle⟩` from `hS u T hu hT`. Establish `ha0 : a 0 = 0`. Establish `h` using `ha 0`. Rewrite `h` using `[ArithmeticFunction.map_zero]`.

Conclude with `norm_le_zero_iff.mp h`. Establish `hΛsum : Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c)`. Establish `h` using `ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (c : ℂ)) (by simpa using hc1)`. Use `Complex.summable_ofReal.mp (h.congr (fun n => ?_))` and prove the remaining obligations. Break down `eq_or_ne n 0 with rfl | hn` into its components or cases.

Simplify using the standard rewrite rules. Rewrite using `[LSeries.term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg _)]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hterm : ∀ (n : ℕ) (s : ℂ), s.re = c → ‖LSeries.term a s n‖ ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c`.

Introduce `n s hs`. Rewrite using `[LSeries.norm_term_eq, hs]`. Use `split_ifs with hn`. Substitute `hn` using the available equality. Simplify using the standard rewrite rules.

Conclude with `div_le_div_of_nonneg_right (ha n) (by positivity)`. Establish `hre : ∀ t : ℝ, ((c : ℂ) + t * I).re = c` using `by intro t; simp`. Establish `hkern : ∀ t : ℝ, ‖(u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)‖ ≤ u ^ c / c`. Introduce `t`. Rewrite using `[norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hu0, hre]`.

Apply `div_le_div_of_nonneg_left (by positivity) hc0` to reduce the goal to its premises. Establish `h` using `Complex.abs_re_le_norm ((c : ℂ) + t * I)`. Rewrite `h` using `[hre, abs_of_pos hc0]`. Conclude with `h`. Establish `hDC` using `intervalIntegral.hasSum_integral_of_dominated_convergence (μ := MeasureTheory.volume) (a := -T) (b := T) (F := fun (n : ℕ) (t : ℝ) => LSeries.term a ((c : ℂ) + t * I) n * ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))) (f := fun t : ℝ => LSeries a ((c : ℂ) + t * I) * ((u : ℂ) …`.

Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using `only [LSeries.term_zero, zero_mul]`. Conclude with `MeasureTheory.aestronglyMeasurable_const`. Simplify using `only [LSeries.term_of_ne_zero hn]`. Apply `Measurable.aestronglyMeasurable` to reduce the goal to its premises.

Use the proof step `fun_prop)`. Use the proof step `(fun n => Filter.Eventually.of_forall (fun t _ => by`. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (hterm n _ (hre t)) (hkern t) (norm_nonneg _) (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))))`. Use the proof step `(Filter.Eventually.of_forall (fun t _ => hΛsum.mul_right _))`.

Use `intervalIntegrable_const`. Use the proof step `(Filter.Eventually.of_forall (fun t _ => by`. Establish `hsum : LSeriesSummable a ((c : ℂ) + t * I)` using `Summable.of_norm_bounded hΛsum (fun n => hterm n _ (hre t))`. Conclude with `hsum.hasSum.mul_right _))`. Establish `hG : HasSum (fun n : ℕ => a n * perronK (u / n) c T) ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ in (-T)..T, LSeries a ((c : ℂ) + t * I) * ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)))`.

Establish `hfun : (fun n : ℕ => a n * perronK (u / n) c T) = fun n : ℕ => (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ in (-T)..T, LSeries.term a ((c : ℂ) + t * I) n * ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))`. Use function extensionality and compare the values at `n`. Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using `[ha0, LSeries.term_zero]`. Establish `h1 : (∫ t : ℝ in (-T)..T, LSeries.term a ((c : ℂ) + t * I) n * ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))) = a n * ∫ t : ℝ in (-T)..T, ((u / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)`.

Rewrite using `[← intervalIntegral.integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `t`. Conclude with `term_mul_kernel a u hu0 n hn _`. Rewrite using `[h1, perronK]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfun]`. Conclude with `hDC.mul_left _`. Establish `hind : HasSum (fun n : ℕ => a n * (if 1 ≤ u / n then (1 : ℂ) else 0)) (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n)`. Establish `h : HasSum (fun n : ℕ => a n * (if 1 ≤ u / n then (1 : ℂ) else 0)) (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n * (if 1 ≤ u / n then (1 : ℂ) else 0))`.

Apply `hasSum_sum_of_ne_finset_zero` to reduce the goal to its premises. Introduce `n hn`. Rewrite `hn` using `[Finset.mem_Icc, not_and_or]`. Break down `hn with hn | hn` into its components or cases. Establish `hn0 : n = 0` using `by omega`.

Substitute `hn0` using the available equality. Simplify using `[ha0]`. Use `push_neg at hn`. Establish `hlt : u < n`. Establish `h1` using `Nat.lt_floor_add_one u`.

Establish `h2 : (⌊u⌋₊ : ℝ) + 1 ≤ n` using `by exact_mod_cast hn`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : ¬ (1 ≤ u / n)`. Rewrite using `[not_le, div_lt_one (by linarith)]`. Conclude with `hlt`.

Simplify using `[h3]`. Use `h using 1` and compare the differences between its conclusion and the goal. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `n hn`. Rewrite `hn` using `[Finset.mem_Icc]`.

Establish `hn1 : (1 : ℝ) ≤ n` using `by exact_mod_cast hn.1`. Establish `hnu : (n : ℝ) ≤ u` using `le_trans (by exact_mod_cast hn.2) (Nat.floor_le hu0.le)`. Establish `h4 : 1 ≤ u / n`. Rewrite using `[le_div_iff₀ (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Simplify using `[h4]`. Establish `hdiff` using `hind.sub hG`. Rewrite using `[← hdiff.tsum_eq]`. Combine the equalities or inequalities in the displayed calculation. Apply `tsum_of_norm_bounded hSs.hasSum` to reduce the goal to its premises.

Introduce `n`. Rewrite using `[← mul_sub, norm_mul]`. Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using `[ha0]`. Establish `hy : 0 < u / n` using `div_pos hu0 (by exact_mod_cast Nat.pos_of_ne_zero hn)`.

Establish `h1` using `kernel_le_kb hK (u / n) c T hy hc0 hT0`. Rewrite `h1` using `[norm_sub_rev]`. Rewrite using `[mul_assoc]`. Conclude with `mul_le_mul (ha n) h1 (norm_nonneg _) ArithmeticFunction.vonMangoldt_nonneg`. Use `_ ≤ _ := hSle`.
-/
theorem perronTrunc_of {C : ℝ} (hK : PerronKernel) (hS : PerronSumBound C) : PerronTrunc C := by
  intro a ha u T hu hT
  have hc1 : 1 < cLine u := one_lt_cLine hu
  set c := cLine u with hcdef
  have hc0 : 0 < c := by linarith
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  obtain ⟨hSs, hSle⟩ := hS u T hu hT
  have ha0 : a 0 = 0 := by
    have h := ha 0
    rw [ArithmeticFunction.map_zero] at h
    exact norm_le_zero_iff.mp h

  have hΛsum : Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c) := by
    have h := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (c : ℂ)) (by simpa using hc1)
    refine Complex.summable_ofReal.mp (h.congr (fun n => ?_))
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg _)]
      push_cast
      rfl
  have hterm : ∀ (n : ℕ) (s : ℂ), s.re = c →
      ‖LSeries.term a s n‖ ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c := by
    intro n s hs
    rw [LSeries.norm_term_eq, hs]
    split_ifs with hn
    · subst hn
      simp
    · exact div_le_div_of_nonneg_right (ha n) (by positivity)
  have hre : ∀ t : ℝ, ((c : ℂ) + t * I).re = c := by intro t; simp
  have hkern : ∀ t : ℝ, ‖(u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)‖ ≤ u ^ c / c := by
    intro t
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hu0, hre]
    apply div_le_div_of_nonneg_left (by positivity) hc0
    have h := Complex.abs_re_le_norm ((c : ℂ) + t * I)
    rw [hre, abs_of_pos hc0] at h
    exact h

  have hDC := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := MeasureTheory.volume)
    (a := -T) (b := T)
    (F := fun (n : ℕ) (t : ℝ) => LSeries.term a ((c : ℂ) + t * I) n *
      ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)))
    (f := fun t : ℝ => LSeries a ((c : ℂ) + t * I) * ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)))
    (fun n _ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c * (u ^ c / c))
    (fun n => by
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [LSeries.term_zero, zero_mul]
        exact MeasureTheory.aestronglyMeasurable_const
      · simp only [LSeries.term_of_ne_zero hn]
        apply Measurable.aestronglyMeasurable
        fun_prop)
    (fun n => Filter.Eventually.of_forall (fun t _ => by
      rw [norm_mul]
      exact mul_le_mul (hterm n _ (hre t)) (hkern t) (norm_nonneg _)
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))))
    (Filter.Eventually.of_forall (fun t _ => hΛsum.mul_right _))
    intervalIntegrable_const
    (Filter.Eventually.of_forall (fun t _ => by
      have hsum : LSeriesSummable a ((c : ℂ) + t * I) :=
        Summable.of_norm_bounded hΛsum (fun n => hterm n _ (hre t))
      exact hsum.hasSum.mul_right _))

  have hG : HasSum (fun n : ℕ => a n * perronK (u / n) c T)
      ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ in (-T)..T, LSeries a ((c : ℂ) + t * I) *
        ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))) := by
    have hfun : (fun n : ℕ => a n * perronK (u / n) c T) = fun n : ℕ => (1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ in (-T)..T, LSeries.term a ((c : ℂ) + t * I) n *
          ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) := by
      funext n
      rcases eq_or_ne n 0 with rfl | hn
      · simp [ha0, LSeries.term_zero]
      · have h1 : (∫ t : ℝ in (-T)..T, LSeries.term a ((c : ℂ) + t * I) n *
              ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))) =
            a n * ∫ t : ℝ in (-T)..T, ((u / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) := by
          rw [← intervalIntegral.integral_const_mul]
          congr 1
          funext t
          exact term_mul_kernel a u hu0 n hn _
        rw [h1, perronK]
        ring
    rw [hfun]
    exact hDC.mul_left _

  have hind : HasSum (fun n : ℕ => a n * (if 1 ≤ u / n then (1 : ℂ) else 0))
      (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n) := by
    have h : HasSum (fun n : ℕ => a n * (if 1 ≤ u / n then (1 : ℂ) else 0))
        (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n * (if 1 ≤ u / n then (1 : ℂ) else 0)) := by
      apply hasSum_sum_of_ne_finset_zero
      intro n hn
      rw [Finset.mem_Icc, not_and_or] at hn
      rcases hn with hn | hn
      · have hn0 : n = 0 := by omega
        subst hn0
        simp [ha0]
      · push_neg at hn
        have hlt : u < n := by
          have h1 := Nat.lt_floor_add_one u
          have h2 : (⌊u⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
          linarith
        have h3 : ¬ (1 ≤ u / n) := by
          rw [not_le, div_lt_one (by linarith)]
          exact hlt
        simp [h3]
    convert h using 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hnu : (n : ℝ) ≤ u := le_trans (by exact_mod_cast hn.2) (Nat.floor_le hu0.le)
    have h4 : 1 ≤ u / n := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    simp [h4]
  have hdiff := hind.sub hG
  rw [← hdiff.tsum_eq]
  calc _ ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (u / n) ^ c * kb T (u / n) := by
        apply tsum_of_norm_bounded hSs.hasSum
        intro n
        rw [← mul_sub, norm_mul]
        rcases eq_or_ne n 0 with rfl | hn
        · simp [ha0]
        · have hy : 0 < u / n := div_pos hu0 (by exact_mod_cast Nat.pos_of_ne_zero hn)
          have h1 := kernel_le_kb hK (u / n) c T hy hc0 hT0
          rw [norm_sub_rev] at h1
          rw [mul_assoc]
          exact mul_le_mul (ha n) h1 (norm_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ _ := hSle

end PI.EF.PK

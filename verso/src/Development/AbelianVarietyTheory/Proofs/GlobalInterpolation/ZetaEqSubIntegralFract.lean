import Mathlib

namespace GlobalTheory.ZetaFractionalIntegral

open MeasureTheory Set Filter Asymptotics

/- English proof (translation)
Establish `hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (fun _ : ℕ ↦ (1 : ℝ)) k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ)`. Use `Asymptotics.isBigO_of_le _ fun n ↦ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `key` using `LSeries_eq_mul_integral_of_nonneg (fun _ ↦ (1 : ℝ)) zero_le_one hs hO (fun _ ↦ zero_le_one)`. Establish `e1 : LSeries (fun n : ℕ ↦ (((fun _ : ℕ ↦ (1 : ℝ)) n : ℝ) : ℂ)) s = riemannZeta s`.

Rewrite using `[← LSeries_one_eq_riemannZeta hs]`. Use `congr 1`. Rewrite using `[← e1, key]`. Use `congr 2`. Use function extensionality and compare the values at `t`.

Simplify using the standard rewrite rules.
-/
lemma zeta_eq_mul_integral_floor {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s * ∫ t in Set.Ioi (1 : ℝ), ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (fun _ : ℕ ↦ (1 : ℝ)) k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.isBigO_of_le _ fun n ↦ ?_
    simp
  have key := LSeries_eq_mul_integral_of_nonneg (fun _ ↦ (1 : ℝ)) zero_le_one hs hO (fun _ ↦ zero_le_one)
  have e1 : LSeries (fun n : ℕ ↦ (((fun _ : ℕ ↦ (1 : ℝ)) n : ℝ) : ℂ)) s = riemannZeta s := by
    rw [← LSeries_one_eq_riemannZeta hs]
    congr 1
  rw [← e1, key]
  congr 2
  funext t
  simp

/- English proof (translation)
The claim follows from `integrableOn_Ioi_cpow_of_lt (by simp only [Complex.neg_re]; linarith) one_pos`.
-/
lemma integrableOn_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Set.Ioi 1) := integrableOn_Ioi_cpow_of_lt (by simp only [Complex.neg_re]; linarith) one_pos

/- English proof (translation)
Establish `hg : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1)` using `integrableOn_Ioi_cpow_of_lt (by simp only [Complex.neg_re, Complex.add_re, Complex.one_re]; linarith) one_pos`. Use `MeasureTheory.Integrable.mono hg (((Complex.measurable_ofReal.comp measurable_fract).aestronglyMeasurable).mul hg.aestronglyMeasurable) (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Establish `h0` using `Int.fract_nonneg t`. Establish `h1` using `Int.fract_lt_one t`.

Establish `: ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1`. Rewrite using `[Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]`. Conclude with `h1.le`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma integrableOn_fract_mul {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
  have hg : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp only [Complex.neg_re, Complex.add_re, Complex.one_re]; linarith) one_pos
  refine MeasureTheory.Integrable.mono hg (((Complex.measurable_ofReal.comp measurable_fract).aestronglyMeasurable).mul
    hg.aestronglyMeasurable) (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_mul]
  have h0 := Int.fract_nonneg t
  have h1 := Int.fract_lt_one t
  have : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1.le
  calc ‖((Int.fract t : ℝ) : ℂ)‖ * ‖(t : ℂ) ^ (-(s + 1))‖ ≤ 1 * ‖(t : ℂ) ^ (-(s + 1))‖ :=
        mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ = ‖(t : ℂ) ^ (-(s + 1))‖ := one_mul _

/- English proof (translation)
Introduce `d1 s hs`. Simplify using `only [d1]`. Establish `hA` using `integrableOn_cpow_neg hs`. Establish `hB` using `integrableOn_fract_mul hs`. Establish `hsplit : ∫ t in Set.Ioi (1 : ℝ), ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1)) = (∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s)) - ∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))`.

Rewrite using `[← integral_sub hA hB]`. Use `setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_` and prove the remaining obligations. Establish `ht0 : (0 : ℝ) < t` using `lt_trans one_pos ht`. Establish `hfl : ((⌊t⌋₊ : ℕ) : ℝ) = t - Int.fract t`. Rewrite using `[Int.self_sub_fract, natCast_floor_eq_intCast_floor ht0.le]`.

Establish `hpow : (t : ℂ) ^ (-s) = (t : ℂ) * (t : ℂ) ^ (-(s + 1))`. Rewrite using `[show -s = -(s + 1) + 1 by ring, Complex.cpow_add _ _ (by exact_mod_cast ht0.ne'), Complex.cpow_one, mul_comm]`. Establish `hfl' : ((⌊t⌋₊ : ℕ) : ℂ) = (t : ℂ) - ((Int.fract t : ℝ) : ℂ)`. Rewrite using `[← Complex.ofReal_natCast, hfl, Complex.ofReal_sub]`. Rewrite using `[hpow, hfl']`.

Expand and normalize the polynomial expressions, which then agree. Establish `hI : ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s) = 1 / (s - 1)`. Rewrite using `[integral_Ioi_cpow_of_lt (by simp only [Complex.neg_re]; linarith) one_pos, Complex.ofReal_one, Complex.one_cpow, show -s + 1 = -(s - 1) by ring, div_neg, neg_div, neg_neg]`. Rewrite using `[zeta_eq_mul_integral_floor hs, hsplit, hI]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zeta_eq_sub_integral_fract :
    (let d1 : ℂ → ℂ := @(fun (s : ℂ) ↦ ∫ (t : ℝ) in Set.Ioi (1 : ℝ), (↑(Int.fract t) : ℂ) * (↑t : ℂ) ^ (-(s + (1 : ℂ)))); ∀ {s : ℂ}, (1 : ℝ) < Complex.re s → riemannZeta s = s / (s - (1 : ℂ)) - s * d1 s) := by
  intro d1 s hs
  simp only [d1]
  have hA := integrableOn_cpow_neg hs
  have hB := integrableOn_fract_mul hs
  have hsplit : ∫ t in Set.Ioi (1 : ℝ), ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      (∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s)) -
        ∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    rw [← integral_sub hA hB]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
    have hfl : ((⌊t⌋₊ : ℕ) : ℝ) = t - Int.fract t := by
      rw [Int.self_sub_fract, natCast_floor_eq_intCast_floor ht0.le]
    have hpow : (t : ℂ) ^ (-s) = (t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
      rw [show -s = -(s + 1) + 1 by ring, Complex.cpow_add _ _ (by exact_mod_cast ht0.ne'), Complex.cpow_one,
        mul_comm]
    have hfl' : ((⌊t⌋₊ : ℕ) : ℂ) = (t : ℂ) - ((Int.fract t : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, hfl, Complex.ofReal_sub]
    rw [hpow, hfl']
    ring
  have hI : ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s) = 1 / (s - 1) := by
    rw [integral_Ioi_cpow_of_lt (by simp only [Complex.neg_re]; linarith) one_pos, Complex.ofReal_one,
      Complex.one_cpow, show -s + 1 = -(s - 1) by ring, div_neg, neg_div, neg_neg]
  rw [zeta_eq_mul_integral_floor hs, hsplit, hI]
  ring

end GlobalTheory.ZetaFractionalIntegral

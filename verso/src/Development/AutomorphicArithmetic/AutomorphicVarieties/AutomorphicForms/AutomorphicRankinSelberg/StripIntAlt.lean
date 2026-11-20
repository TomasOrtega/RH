import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open MeasureTheory Set
open UpperHalfPlane hiding I
open scoped MatrixGroups

/- English proof (translation)
Establish `hsplit : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0` using `Ioc_union_Ioi_eq_Ioi zero_le_one`. Rewrite using `[← hsplit]`. Use `IntegrableOn.union ?_ ?_` and prove the remaining obligations. Establish `h1 : IntegrableOn (fun y : ℝ => y ^ (s - 2)) (Ioc 0 1)` using `(intervalIntegral.intervalIntegrable_rpow' (by linarith)).1.mono_set (le_of_eq (uIoc_of_le zero_le_one).symm)`. Establish `h1' : IntegrableOn (fun y : ℝ => A * y ^ (s - 2)) (Ioc 0 1)` using `h1.const_mul A`.

Use `h1'.congr_fun ?_ measurableSet_Ioc` and prove the remaining obligations. Introduce `y hy`. Establish `hy0 : 0 < y` using `hy.1`. Simplify using `only [if_pos hy.2]`. Rewrite using `[Real.rpow_sub hy0, Real.rpow_two, mul_div_assoc]`.

Establish `h2 : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Ioi 1)` using `integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one`. Establish `h2' : IntegrableOn (fun y : ℝ => B * y ^ (-2 : ℝ)) (Ioi 1)` using `h2.const_mul B`. Use `h2'.congr_fun ?_ measurableSet_Ioi` and prove the remaining obligations. Introduce `y hy`. Establish `hy1 : (1:ℝ) < y` using `hy`.

Establish `hy0 : 0 < y` using `by linarith`. Simplify using `only [if_neg (not_le.mpr hy1)]`. Rewrite using `[Real.rpow_neg hy0.le, Real.rpow_two, div_eq_mul_inv]`.
-/
private lemma UpperTheory.V.Af.Rs.stripInt_maj (A B s : ℝ) (hs : 1 < s) :
    IntegrableOn (fun y : ℝ => (if y ≤ 1 then A * y ^ s else B) / y ^ 2) (Ioi 0) := by
  have hsplit : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := Ioc_union_Ioi_eq_Ioi zero_le_one
  rw [← hsplit]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntegrableOn (fun y : ℝ => y ^ (s - 2)) (Ioc 0 1) :=
      (intervalIntegral.intervalIntegrable_rpow' (by linarith)).1.mono_set
        (le_of_eq (uIoc_of_le zero_le_one).symm)
    have h1' : IntegrableOn (fun y : ℝ => A * y ^ (s - 2)) (Ioc 0 1) := h1.const_mul A
    refine h1'.congr_fun ?_ measurableSet_Ioc
    intro y hy
    have hy0 : 0 < y := hy.1
    simp only [if_pos hy.2]
    rw [Real.rpow_sub hy0, Real.rpow_two, mul_div_assoc]
  · have h2 : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
    have h2' : IntegrableOn (fun y : ℝ => B * y ^ (-2 : ℝ)) (Ioi 1) := h2.const_mul B
    refine h2'.congr_fun ?_ measurableSet_Ioi
    intro y hy
    have hy1 : (1:ℝ) < y := hy
    have hy0 : 0 < y := by linarith
    simp only [if_neg (not_le.mpr hy1)]
    rw [Real.rpow_neg hy0.le, Real.rpow_two, div_eq_mul_inv]

/- English proof (translation)
Introduce `hIm F hF s hs`. Take `⟨hcont, C, hC⟩` from `hF`. Establish `hbound : ∀ z : ℍ, ‖F z‖ ≤ 8 * C`. Introduce `z`. Take `⟨g, hg⟩` from `ModularGroup.exists_smul_mem_fd z`.

Establish `h4` using `ModularGroup.three_le_four_mul_im_sq_of_mem_fd hg`. Establish `hpos` using `(g • z).im_pos`. Establish `hw : 1 / 2 ≤ (g • z).im` using `by nlinarith`. Establish `hC'` using `hC g⁻¹ (g • z) hw`. Rewrite `hC'` using `[inv_smul_smul]`.

Establish `h3 : (1 / 2 : ℝ) ^ 3 ≤ (g • z).im ^ 3` using `pow_le_pow_left₀ (by norm_num) hw 3`. Use polynomial arithmetic with `[norm_nonneg (F z)]`. Establish `hhigh : ∀ z : ℍ, 1 < z.im → ‖F z‖ * z.im ^ s ≤ C`. Introduce `z hz`. Establish `hC'` using `hC 1 z (by linarith)`.

Rewrite `hC'` using `[one_smul]`. Establish `hle : z.im ^ s ≤ z.im ^ (3 : ℕ)`. Rewrite using `[← Real.rpow_natCast]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hz.le (by push_cast; linarith [hs.2])`. Combine the equalities or inequalities in the displayed calculation.

Establish `hmeas : Measurable (fun y : ℝ => if y ≤ 1 then 8 * C * y ^ s else C)` using `Measurable.ite measurableSet_Iic ((measurable_id.pow_const s).const_mul _) measurable_const`. Establish `hφ` using `hIm _ hmeas (UpperTheory.V.Af.Rs.stripInt_maj (8 * C) C s hs.1)`. Use `Integrable.mono' hφ ?_ ?_` and prove the remaining obligations. Establish `hc : Continuous fun z : ℍ => F z * ((z.im ^ s : ℝ) : ℂ)` using `hcont.mul (Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_im.rpow_const fun _ => Or.inr (by linarith [hs.1])))`. Conclude with `hc.aestronglyMeasurable`.

Use `Filter.Eventually.of_forall fun z => ?_` and prove the remaining obligations. Establish `hy` using `z.im_pos`. Rewrite using `[norm_mul, Complex.norm_of_nonneg (Real.rpow_nonneg hy.le s)]`. Use `split_ifs with h`. Conclude with `mul_le_mul_of_nonneg_right (hbound z) (Real.rpow_nonneg hy.le s)`.

Conclude with `hhigh z (not_le.mp h)`.
-/
theorem UpperTheory.V.Af.Rs.stripInt :
    UpperTheory.V.Af.Rs.StripIm → UpperTheory.V.Af.Rs.StripInt := by
  intro hIm F hF s hs
  obtain ⟨hcont, C, hC⟩ := hF
  have hbound : ∀ z : ℍ, ‖F z‖ ≤ 8 * C := by
    intro z
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
    have h4 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hg
    have hpos := (g • z).im_pos
    have hw : 1 / 2 ≤ (g • z).im := by nlinarith
    have hC' := hC g⁻¹ (g • z) hw
    rw [inv_smul_smul] at hC'
    have h3 : (1 / 2 : ℝ) ^ 3 ≤ (g • z).im ^ 3 := pow_le_pow_left₀ (by norm_num) hw 3
    nlinarith [norm_nonneg (F z)]
  have hhigh : ∀ z : ℍ, 1 < z.im → ‖F z‖ * z.im ^ s ≤ C := by
    intro z hz
    have hC' := hC 1 z (by linarith)
    rw [one_smul] at hC'
    have hle : z.im ^ s ≤ z.im ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hz.le (by push_cast; linarith [hs.2])
    calc ‖F z‖ * z.im ^ s ≤ ‖F z‖ * z.im ^ 3 :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ ≤ C := hC'
  have hmeas : Measurable (fun y : ℝ => if y ≤ 1 then 8 * C * y ^ s else C) :=
    Measurable.ite measurableSet_Iic ((measurable_id.pow_const s).const_mul _) measurable_const
  have hφ := hIm _ hmeas (UpperTheory.V.Af.Rs.stripInt_maj (8 * C) C s hs.1)
  refine Integrable.mono' hφ ?_ ?_
  · have hc : Continuous fun z : ℍ => F z * ((z.im ^ s : ℝ) : ℂ) :=
      hcont.mul (Complex.continuous_ofReal.comp
        (UpperHalfPlane.continuous_im.rpow_const fun _ => Or.inr (by linarith [hs.1])))
    exact hc.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    have hy := z.im_pos
    rw [norm_mul, Complex.norm_of_nonneg (Real.rpow_nonneg hy.le s)]
    split_ifs with h
    · exact mul_le_mul_of_nonneg_right (hbound z) (Real.rpow_nonneg hy.le s)
    · exact hhigh z (not_le.mp h)

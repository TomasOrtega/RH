import ReciprocityTheory.Chebotarev.UnitPart

open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem

open scoped Classical

namespace ReciprocityTheory.Cheb

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Use `set b := (basisUnitLattice E).ofZLatticeBasis ℝ (unitLattice E) with hb`. Use `⟨∑ i, ‖b i‖, Finset.sum_nonneg fun i _ => norm_nonneg _, fun x hx w => ?_⟩` and prove the remaining obligations. Establish `hsum : (∑ i, ucoord x i • b i) = logMap x`. Simplify `b.sum_repr (logMap x)` using `[ucoord, hb]`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Rewrite using `[_root_.norm_smul, Real.norm_eq_abs]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (hx i).le`.
-/
theorem exists_logMap_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : mixedSpace E, (∀ i, |ucoord x i| < 1) →
    ∀ w : {w : InfinitePlace E // w ≠ w₀}, |logMap x w| ≤ B := by
  set b := (basisUnitLattice E).ofZLatticeBasis ℝ (unitLattice E) with hb
  refine ⟨∑ i, ‖b i‖, Finset.sum_nonneg fun i _ => norm_nonneg _, fun x hx w => ?_⟩
  have hsum : (∑ i, ucoord x i • b i) = logMap x := by
    simpa [ucoord, hb] using b.sum_repr (logMap x)
  calc |logMap x w| = ‖logMap x w‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖logMap x‖ := norm_le_pi_norm (logMap x) w
    _ = ‖∑ i, ucoord x i • b i‖ := by rw [hsum]
    _ ≤ ∑ i, ‖ucoord x i • b i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖b i‖ := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [_root_.norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (hx i).le

/- English proof (translation)
Establish `hne` using `mixedEmbedding.norm_ne_zero_iff.mp hx`. Establish `hlog : Real.log (mixedEmbedding.norm x) = ∑ w : InfinitePlace E, (w.mult : ℝ) * Real.log (normAtPlace w x)`. Rewrite using `[mixedEmbedding.norm_apply, Real.log_prod (fun w _ => pow_ne_zero _ (hne w))]`. Simplify using `[Real.log_pow]`. Establish `hd : (Module.finrank ℚ E : ℝ) ≠ 0`.

Conclude with `(Module.finrank_pos (R := ℚ) (M := E)).ne'` after adjusting the coercions. Establish `hm : (∑ w : InfinitePlace E, (w.mult : ℝ)) = Module.finrank ℚ E`. Conclude with `InfinitePlace.sum_mult_eq` after adjusting the coercions. Repeatedly rewrite using `[mul_sub, Finset.sum_sub_distrib]`. Rewrite using `[← hlog, ← Finset.sum_mul, hm]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_mult_logDev {x : mixedSpace E} (hx : mixedEmbedding.norm x ≠ 0) :
    ∑ w : InfinitePlace E, (w.mult : ℝ) * (Real.log (normAtPlace w x) -
      Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ E : ℝ)⁻¹) = 0 := by
  have hne := mixedEmbedding.norm_ne_zero_iff.mp hx
  have hlog : Real.log (mixedEmbedding.norm x) =
      ∑ w : InfinitePlace E, (w.mult : ℝ) * Real.log (normAtPlace w x) := by
    rw [mixedEmbedding.norm_apply, Real.log_prod (fun w _ => pow_ne_zero _ (hne w))]
    simp [Real.log_pow]
  have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E)).ne'
  have hm : (∑ w : InfinitePlace E, (w.mult : ℝ)) = Module.finrank ℚ E := by
    exact_mod_cast InfinitePlace.sum_mult_eq
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [← hlog, ← Finset.sum_mul, hm]
  field_simp
  ring

/- English proof (translation)
Take `⟨B, hB0, hB⟩` from `exists_logMap_bound (E := E)`. Use `⟨Fintype.card (InfinitePlace E) * B, by positivity, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hN : mixedEmbedding.norm x ≠ 0` using `fun h => hx (by simp [uphi, h])`. Establish `hT : Tent (ucoord x) ≠ 0` using `by simpa [uphi, hN] using hx`. Establish `hc : ∀ i, |ucoord x i| < 1` using `abs_lt_one_of_Tent_ne_zero hT`.

Use `⟨hN, fun w => ?_⟩` and prove the remaining obligations. Use `set D : InfinitePlace E → ℝ := fun w => Real.log (normAtPlace w x) - Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ E : ℝ)⁻¹ with hD`. Establish `hlm : ∀ v : {w : InfinitePlace E // w ≠ w₀}, logMap x v = (v.1.mult : ℝ) * D v.1` using `fun v => rfl`. Establish `hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace E)`. Conclude with `Fintype.card_pos` after adjusting the coercions.

Establish `key : |(w.mult : ℝ) * D w| ≤ Fintype.card (InfinitePlace E) * B`. Distinguish the cases in `hw : w = w₀`. Rewrite using `[hw]`. Establish `h0` using `sum_mult_logDev hN`. Rewrite `h0` using `[Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace E)]`.

Establish `h1 : ((w₀ : InfinitePlace E).mult : ℝ) * D w₀ = -∑ v : {w : InfinitePlace E // w ≠ w₀}, logMap x v`. Simplify using `only [hlm]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[h1, abs_neg]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `Fintype.card_subtype_le _` after adjusting the coercions. Use `hB x hc ⟨w, hw⟩` as an intermediate fact. Rewrite `this` using `[hlm]`. Conclude with `this.trans (le_mul_of_one_le_left hB0 hcard)`. Establish `hm : (1 : ℝ) ≤ w.mult` using `InfinitePlace.one_le_mult`.

Rewrite `key` using `[abs_mul, abs_of_pos (by linarith : (0:ℝ) < w.mult)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_logDev_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : mixedSpace E, uphi x ≠ 0 →
    mixedEmbedding.norm x ≠ 0 ∧ ∀ w : InfinitePlace E, |Real.log (normAtPlace w x) -
      Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ E : ℝ)⁻¹| ≤ C := by
  obtain ⟨B, hB0, hB⟩ := exists_logMap_bound (E := E)
  refine ⟨Fintype.card (InfinitePlace E) * B, by positivity, fun x hx => ?_⟩
  have hN : mixedEmbedding.norm x ≠ 0 := fun h => hx (by simp [uphi, h])
  have hT : Tent (ucoord x) ≠ 0 := by simpa [uphi, hN] using hx
  have hc : ∀ i, |ucoord x i| < 1 := abs_lt_one_of_Tent_ne_zero hT
  refine ⟨hN, fun w => ?_⟩
  set D : InfinitePlace E → ℝ := fun w => Real.log (normAtPlace w x) -
      Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ E : ℝ)⁻¹ with hD
  have hlm : ∀ v : {w : InfinitePlace E // w ≠ w₀}, logMap x v = (v.1.mult : ℝ) * D v.1 := fun v => rfl
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace E) := by
    exact_mod_cast Fintype.card_pos

  have key : |(w.mult : ℝ) * D w| ≤ Fintype.card (InfinitePlace E) * B := by
    by_cases hw : w = w₀
    · rw [hw]
      have h0 := sum_mult_logDev hN
      rw [Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace E)] at h0
      have h1 : ((w₀ : InfinitePlace E).mult : ℝ) * D w₀ = -∑ v : {w : InfinitePlace E // w ≠ w₀}, logMap x v := by
        simp only [hlm]; linarith
      rw [h1, abs_neg]
      calc |∑ v : {w : InfinitePlace E // w ≠ w₀}, logMap x v|
          ≤ ∑ v : {w : InfinitePlace E // w ≠ w₀}, |logMap x v| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _v : {w : InfinitePlace E // w ≠ w₀}, B := Finset.sum_le_sum fun v _ => hB x hc v
        _ = Fintype.card {w : InfinitePlace E // w ≠ w₀} * B := by simp
        _ ≤ Fintype.card (InfinitePlace E) * B := by
          gcongr
          exact_mod_cast Fintype.card_subtype_le _
    · have := hB x hc ⟨w, hw⟩
      rw [hlm] at this
      exact this.trans (le_mul_of_one_le_left hB0 hcard)
  have hm : (1 : ℝ) ≤ w.mult := InfinitePlace.one_le_mult
  rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < w.mult)] at key
  calc |D w| ≤ (w.mult : ℝ) * |D w| := le_mul_of_one_le_left (abs_nonneg _) hm
    _ ≤ _ := key

/- English proof (translation)
Take `⟨C, hC0, hC⟩` from `exists_logDev_bound (E := E)`. Use `⟨Real.exp (-(2 * C)), Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith), fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨hN, hD⟩` from `hC x hx`. Establish `hpos : ∀ w, 0 < normAtPlace w x` using `fun w => lt_of_le_of_ne (normAtPlace_nonneg w x) (mixedEmbedding.norm_ne_zero_iff.mp hN w).symm`. Establish `h1 : ∀ w, Real.exp (-(2 * C)) * ‖x‖ ≤ normAtPlace w x`.

Introduce `w`. Take `⟨w', -, hw'⟩` from `Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun w => normAtPlace w x)`. Rewrite using `[norm_eq_sup'_normAtPlace, hw']`. Establish `a` using `hD w`. Establish `b` using `hD w'`.

Rewrite `a`, `b` using `[abs_le]`. Establish `hl : Real.log (normAtPlace w' x) - 2 * C ≤ Real.log (normAtPlace w x)` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.exp_sub, Real.exp_log (hpos w'), Real.exp_neg]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ Real.exp (Real.log (normAtPlace w x)) := Real.exp_le_exp.mpr hl`. Use `_ = normAtPlace w x := Real.exp_log (hpos w)`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_pow, mixedEmbedding.norm_apply, ← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]`. Use `Finset.prod_le_prod (fun w _ => by positivity) fun w _ => ?_` and prove the remaining obligations.

Conclude with `pow_le_pow_left₀ (by positivity) (h1 w) _`.
-/
theorem exists_support_bound : ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ 1 ∧ ∀ x : mixedSpace E, uphi x ≠ 0 →
    (∀ w : InfinitePlace E, c₀ * ‖x‖ ≤ normAtPlace w x) ∧
      c₀ ^ Module.finrank ℚ E * ‖x‖ ^ Module.finrank ℚ E ≤ mixedEmbedding.norm x := by
  obtain ⟨C, hC0, hC⟩ := exists_logDev_bound (E := E)
  refine ⟨Real.exp (-(2 * C)), Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith), fun x hx => ?_⟩
  obtain ⟨hN, hD⟩ := hC x hx
  have hpos : ∀ w, 0 < normAtPlace w x := fun w =>
    lt_of_le_of_ne (normAtPlace_nonneg w x) (mixedEmbedding.norm_ne_zero_iff.mp hN w).symm
  have h1 : ∀ w, Real.exp (-(2 * C)) * ‖x‖ ≤ normAtPlace w x := by
    intro w
    obtain ⟨w', -, hw'⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun w => normAtPlace w x)
    rw [norm_eq_sup'_normAtPlace, hw']
    have a := hD w
    have b := hD w'
    rw [abs_le] at a b
    have hl : Real.log (normAtPlace w' x) - 2 * C ≤ Real.log (normAtPlace w x) := by linarith
    calc Real.exp (-(2 * C)) * normAtPlace w' x
        = Real.exp (Real.log (normAtPlace w' x) - 2 * C) := by
          rw [Real.exp_sub, Real.exp_log (hpos w'), Real.exp_neg]; ring
      _ ≤ Real.exp (Real.log (normAtPlace w x)) := Real.exp_le_exp.mpr hl
      _ = normAtPlace w x := Real.exp_log (hpos w)
  refine ⟨h1, ?_⟩
  rw [← mul_pow, mixedEmbedding.norm_apply, ← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun w _ => by positivity) fun w _ => ?_
  exact pow_le_pow_left₀ (by positivity) (h1 w) _

end ReciprocityTheory.Cheb

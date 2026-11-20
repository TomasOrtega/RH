import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeakStatement

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

/- English proof (translation)
Rewrite using `[← Module.finrank_mul_finrank ℝ ℂ (V n), Complex.finrank_real_complex, finrank_euclideanSpace_fin]`.
-/
theorem finrank_real_V {n : ℕ} : Module.finrank ℝ (V n) = 2 * n := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (V n), Complex.finrank_real_complex, finrank_euclideanSpace_fin]

/- English proof (translation)
Introduce `n s hn`. Use `haveI : Nontrivial (V n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_real_V]; omega)`. Establish `hind : (ball (0 : V n) 1).indicator (fun z : V n => ‖z‖ ^ (-2 * s)) = fun z => (Iio (1 : ℝ)).indicator (fun y : ℝ => y ^ (-2 * s)) ‖z‖`. Use function extensionality and compare the values at `z`. Apply the tactic sequence `by_cases h : ‖z‖ < 1 <;> simp [Set.indicator, mem_ball_zero_iff, h]`.

Rewrite using `[← integrable_indicator_iff measurableSet_ball, hind, integrable_fun_norm_addHaar, finrank_real_V]`. Establish `hfun : (fun y : ℝ => y ^ (2 * n - 1) • (Iio (1 : ℝ)).indicator (fun y : ℝ => y ^ (-2 * s)) y) = (Iio (1 : ℝ)).indicator (fun y : ℝ => y ^ (2 * n - 1) * y ^ (-2 * s))`. Use function extensionality and compare the values at `y`. Simplify using `only [indicator_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[hfun, IntegrableOn, integrable_indicator_iff measurableSet_Iio, IntegrableOn, Measure.restrict_restrict measurableSet_Iio, Set.inter_comm, Set.Ioi_inter_Iio, ← IntegrableOn]`. Establish `hcongr : EqOn (fun y : ℝ => y ^ (2 * n - 1) * y ^ (-2 * s)) (fun y : ℝ => y ^ ((2 * n : ℝ) - 1 - 2 * s)) (Ioo 0 1)`. Introduce `y hy`. Establish `hy0 : 0 < y` using `hy.1`. Simplify using `only`.

Rewrite using `[← Real.rpow_natCast, ← Real.rpow_add hy0]`. Use `congr 1`. Rewrite using `[Nat.cast_sub (by omega : 1 ≤ 2 * n)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[integrableOn_congr_fun hcongr measurableSet_Ioo, intervalIntegral.integrableOn_Ioo_rpow_iff one_pos]`. Apply the tactic sequence `constructor <;> intro h <;> linarith`.
-/
theorem mvPow : MVPowStatement := by
  intro n s hn
  haveI : Nontrivial (V n) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_real_V]; omega)
  have hind : (ball (0 : V n) 1).indicator (fun z : V n => ‖z‖ ^ (-2 * s)) =
      fun z => (Iio (1 : ℝ)).indicator (fun y : ℝ => y ^ (-2 * s)) ‖z‖ := by
    funext z
    by_cases h : ‖z‖ < 1 <;> simp [Set.indicator, mem_ball_zero_iff, h]
  rw [← integrable_indicator_iff measurableSet_ball, hind, integrable_fun_norm_addHaar,
    finrank_real_V]
  have hfun : (fun y : ℝ => y ^ (2 * n - 1) • (Iio (1 : ℝ)).indicator (fun y : ℝ => y ^ (-2 * s)) y) =
      (Iio (1 : ℝ)).indicator (fun y : ℝ => y ^ (2 * n - 1) * y ^ (-2 * s)) := by
    funext y
    simp only [indicator_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hfun, IntegrableOn, integrable_indicator_iff measurableSet_Iio, IntegrableOn,
    Measure.restrict_restrict measurableSet_Iio, Set.inter_comm, Set.Ioi_inter_Iio, ← IntegrableOn]
  have hcongr : EqOn (fun y : ℝ => y ^ (2 * n - 1) * y ^ (-2 * s))
      (fun y : ℝ => y ^ ((2 * n : ℝ) - 1 - 2 * s)) (Ioo 0 1) := by
    intro y hy
    have hy0 : 0 < y := hy.1
    simp only
    rw [← Real.rpow_natCast, ← Real.rpow_add hy0]
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
    push_cast
    ring
  rw [integrableOn_congr_fun hcongr measurableSet_Ioo,
    intervalIntegral.integrableOn_Ioo_rpow_iff one_pos]
  constructor <;> intro h <;> linarith

noncomputable def mvDivIntegrand (n : ℕ) (δ : ℝ) (z : V n) : ℝ≥0∞ :=
  ENNReal.ofReal ((‖z‖ ^ 2 + δ) ^ (-(n : ℝ)))

/- English proof (translation)
Introduce `n hn`. Establish `hpow` using `mvPow n n hn`. Establish `hn' : (0 : ℝ) < n` using `by exact_mod_cast hn`. Use `set f : ℕ → V n → ℝ≥0∞ := fun k z => ENNReal.ofReal ((‖z‖ ^ 2 + 1 / ((k : ℝ) + 1)) ^ (-(n : ℝ))) with hf`. Establish `hmeas : ∀ k, Measurable (f k)` using `fun k => (by fun_prop : Measurable fun z : V n => ENNReal.ofReal ((‖z‖ ^ 2 + 1 / ((k : ℝ) + 1)) ^ (-(n : ℝ))))`.

Establish `hmono : Monotone f`. Introduce `k m hkm z`. Use `show ENNReal.ofReal _ ≤ ENNReal.ofReal _`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Establish `hkm' : (k : ℝ) ≤ m` using `by exact_mod_cast hkm`.

Apply `Real.rpow_le_rpow_of_nonpos (add_pos_of_nonneg_of_pos (sq_nonneg _) (by positivity)) _ (neg_nonpos.mpr (Nat.cast_nonneg _))` to reduce the goal to its premises. Use `gcongr`. Establish `hinf : ∫⁻ z in ball (0 : V n) 1, ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) = ∞`. Assume the negation of the conclusion as `h`. Establish `hlt` using `lt_top_iff_ne_top.mpr h`.

Establish `hint : IntegrableOn (fun z : V n => ‖z‖ ^ (-2 * (n : ℝ))) (ball 0 1)`. Use `⟨(measurable_norm.pow_const _).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal ?_).mpr hlt⟩` and prove the remaining obligations. Conclude with `ae_of_all _ fun z => Real.rpow_nonneg (norm_nonneg z) _`. Conclude with `lt_irrefl _ (hpow.mp hint)`. Establish `hsup : ∀ z : V n, ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) ≤ ⨆ k, f k z`.

Introduce `z`. Distinguish the cases in `hz : z = 0`. Substitute `hz` using the available equality. Rewrite using `[norm_zero, Real.zero_rpow (by linarith), ENNReal.ofReal_zero]`. Conclude with `zero_le`.

Establish `hz' : 0 < ‖z‖` using `norm_pos_iff.mpr hz`. Establish `h1 : Tendsto (fun k : ℕ => ‖z‖ ^ 2 + 1 / ((k : ℝ) + 1)) atTop (𝓝 (‖z‖ ^ 2 + 0))` using `tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat`. Establish `h2` using `h1.rpow_const (p := -(n : ℝ)) (Or.inl (by positivity))`. Establish `ht : Tendsto (fun k : ℕ => f k z) atTop (𝓝 (ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ)))))` using `by show Tendsto (fun k : ℕ => ENNReal.ofReal ((‖z‖ ^ 2 + 1 / ((k : ℝ) + 1)) ^ (-(n : ℝ)))) atTop _`. Apply `ENNReal.tendsto_ofReal` to reduce the goal to its premises.

Use `h2 using 2` and compare the differences between its conclusion and the goal. Rewrite using `[add_zero, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg z)]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `le_of_tendsto' ht (fun k => le_iSup (fun k => f k z) k)`. Establish `hbig : ⨆ k, ∫⁻ z in ball (0 : V n) 1, f k z = ∞`. Rewrite using `[← lintegral_iSup hmeas hmono]`. Use `top_le_iff.mp ?_` and prove the remaining obligations. Rewrite using `[← hinf]`.

Conclude with `lintegral_mono hsup`. Rewrite using `[ENNReal.tendsto_nhds_top_iff_nnreal]`. Introduce `M`. Establish `hM : (M : ℝ≥0∞) < ⨆ k, ∫⁻ z in ball (0 : V n) 1, f k z`. Rewrite using `[hbig]`.

Conclude with `ENNReal.coe_lt_top`. Take `⟨k, hk⟩` from `lt_iSup_iff.mp hM`. Use `filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity)] with δ hδ`. Use `hk.trans_le (lintegral_mono fun z => ?_)` and prove the remaining obligations. Use `show ENNReal.ofReal _ ≤ ENNReal.ofReal _`.

Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Conclude with `Real.rpow_le_rpow_of_nonpos (add_pos_of_nonneg_of_pos (sq_nonneg _) hδ.1) (by linarith [hδ.2]) (neg_nonpos.mpr (Nat.cast_nonneg _))`.
-/
theorem mvDiv : MVDivStatement := by
  intro n hn
  have hpow := mvPow n n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set f : ℕ → V n → ℝ≥0∞ := fun k z => ENNReal.ofReal ((‖z‖ ^ 2 + 1 / ((k : ℝ) + 1)) ^ (-(n : ℝ)))
    with hf
  have hmeas : ∀ k, Measurable (f k) := fun k =>
    (by fun_prop : Measurable fun z : V n => ENNReal.ofReal ((‖z‖ ^ 2 + 1 / ((k : ℝ) + 1)) ^ (-(n : ℝ))))
  have hmono : Monotone f := by
    intro k m hkm z
    show ENNReal.ofReal _ ≤ ENNReal.ofReal _
    apply ENNReal.ofReal_le_ofReal
    have hkm' : (k : ℝ) ≤ m := by exact_mod_cast hkm
    apply Real.rpow_le_rpow_of_nonpos (add_pos_of_nonneg_of_pos (sq_nonneg _) (by positivity)) _
      (neg_nonpos.mpr (Nat.cast_nonneg _))
    gcongr
  have hinf : ∫⁻ z in ball (0 : V n) 1, ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) = ∞ := by
    by_contra h
    have hlt := lt_top_iff_ne_top.mpr h
    have hint : IntegrableOn (fun z : V n => ‖z‖ ^ (-2 * (n : ℝ))) (ball 0 1) := by
      refine ⟨(measurable_norm.pow_const _).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal ?_).mpr hlt⟩
      exact ae_of_all _ fun z => Real.rpow_nonneg (norm_nonneg z) _
    exact lt_irrefl _ (hpow.mp hint)
  have hsup : ∀ z : V n, ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) ≤ ⨆ k, f k z := by
    intro z
    by_cases hz : z = 0
    · subst hz
      rw [norm_zero, Real.zero_rpow (by linarith), ENNReal.ofReal_zero]
      exact zero_le
    · have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have h1 : Tendsto (fun k : ℕ => ‖z‖ ^ 2 + 1 / ((k : ℝ) + 1)) atTop (𝓝 (‖z‖ ^ 2 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := h1.rpow_const (p := -(n : ℝ)) (Or.inl (by positivity))
      have ht : Tendsto (fun k : ℕ => f k z) atTop (𝓝 (ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))))) := by
        show Tendsto (fun k : ℕ => ENNReal.ofReal ((‖z‖ ^ 2 + 1 / ((k : ℝ) + 1)) ^ (-(n : ℝ)))) atTop _
        apply ENNReal.tendsto_ofReal
        convert h2 using 2
        rw [add_zero, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg z)]
        congr 1
        push_cast
        ring
      exact le_of_tendsto' ht (fun k => le_iSup (fun k => f k z) k)
  have hbig : ⨆ k, ∫⁻ z in ball (0 : V n) 1, f k z = ∞ := by
    rw [← lintegral_iSup hmeas hmono]
    refine top_le_iff.mp ?_
    rw [← hinf]
    exact lintegral_mono hsup
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  intro M
  have hM : (M : ℝ≥0∞) < ⨆ k, ∫⁻ z in ball (0 : V n) 1, f k z := by
    rw [hbig]
    exact ENNReal.coe_lt_top
  obtain ⟨k, hk⟩ := lt_iSup_iff.mp hM
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity)] with δ hδ
  refine hk.trans_le (lintegral_mono fun z => ?_)
  show ENNReal.ofReal _ ≤ ENNReal.ofReal _
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow_of_nonpos (add_pos_of_nonneg_of_pos (sq_nonneg _) hδ.1)
    (by linarith [hδ.2]) (neg_nonpos.mpr (Nat.cast_nonneg _))

end ReciprocityTheory.L2DbarEstimates.C

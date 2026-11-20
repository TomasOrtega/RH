import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement

universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Module Set
open scoped ENNReal ContDiff

/- English proof (translation)
Rewrite using `[finrank_real_of_complex, finrank_euclideanSpace_fin]`.
-/
theorem polar_finrank (n : ℕ) : finrank ℝ (V n) = 2 * n := by
  rw [finrank_real_of_complex, finrank_euclideanSpace_fin]

/- English proof (translation)
The claim follows from `Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [polar_finrank]; omega)`.
-/
private theorem nontrivial_V_of_one_le (n : ℕ) (hn : 1 ≤ n) : Nontrivial (ReciprocityTheory.L2DbarEstimates.V n) :=
  Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [polar_finrank]; omega)

/- English proof (translation)
Establish `hG : Real.Gamma (((2 * n : ℕ) : ℝ) / 2 + 1) = (n.factorial : ℝ)`. Rewrite using `[show ((2 * n : ℕ) : ℝ) / 2 + 1 = (n : ℝ) + 1 by push_cast; ring]`. Conclude with `Real.Gamma_nat_eq_factorial n`. Establish `hs : Real.sqrt Real.pi ^ (2 * n) = Real.pi ^ n`. Rewrite using `[pow_mul, Real.sq_sqrt Real.pi_pos.le]`.

Establish `hpos : (0 : ℝ) ≤ Real.pi ^ n / (n.factorial : ℝ)` using `by positivity`. Use `nontrivial_V_of_one_le n hn` as an intermediate fact. Rewrite using `[measureReal_def, InnerProductSpace.volume_ball, polar_finrank, hG, hs, ENNReal.ofReal_one, one_pow, one_mul, ENNReal.toReal_ofReal hpos]`.
-/
theorem polar_ballReal (n : ℕ) (hn : 1 ≤ n) :
    (volume : Measure (V n)).real (ball 0 1) = Real.pi ^ n / (Nat.factorial n : ℝ) := by
  have hG : Real.Gamma (((2 * n : ℕ) : ℝ) / 2 + 1) = (n.factorial : ℝ) := by
    rw [show ((2 * n : ℕ) : ℝ) / 2 + 1 = (n : ℝ) + 1 by push_cast; ring]
    exact Real.Gamma_nat_eq_factorial n
  have hs : Real.sqrt Real.pi ^ (2 * n) = Real.pi ^ n := by
    rw [pow_mul, Real.sq_sqrt Real.pi_pos.le]
  have hpos : (0 : ℝ) ≤ Real.pi ^ n / (n.factorial : ℝ) := by positivity
  have := nontrivial_V_of_one_le n hn
  rw [measureReal_def, InnerProductSpace.volume_ball, polar_finrank, hG, hs,
    ENNReal.ofReal_one, one_pow, one_mul, ENNReal.toReal_ofReal hpos]

/- English proof (translation)
Establish `hsa : 0 < Real.sqrt a` using `Real.sqrt_pos.mpr ha`. Establish `hb : 0 < b` using `ha.trans_le hab`. Establish `hsb : 0 < Real.sqrt b` using `Real.sqrt_pos.mpr hb`. Establish `hsab : Real.sqrt a ≤ Real.sqrt b` using `Real.sqrt_le_sqrt hab`. Establish `hpt : ∀ y : ℝ, y ^ (2 * n - 1) • (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) y = (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => t⁻¹) y`.

Introduce `y`. Rewrite using `[Set.indicator_apply, Set.indicator_apply]`. Distinguish the cases in `hy : y ∈ Icc (Real.sqrt a) (Real.sqrt b)`. Rewrite using `[if_pos hy, if_pos hy]`. Establish `hy0 : 0 < y` using `hsa.trans_le hy.1`.

Rewrite using `[smul_eq_mul, Real.rpow_neg (by positivity), Real.rpow_natCast]`. Take `⟨k, rfl⟩ : ∃ k, n = k + 1` from `⟨n - 1, by omega⟩`. Rewrite using `[show 2 * (k + 1) - 1 = 2 * k + 1 by omega]`. Establish `hsplit : (y ^ 2) ^ (k + 1) = y ^ (2 * k + 1) * y` using `by ring`. Rewrite using `[hsplit, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hy0.ne'), one_mul]`.

Rewrite using `[if_neg hy, if_neg hy, smul_zero]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `congrArg _ (funext hpt)`. Use `_ = ∫ y in Icc (Real.sqrt a) (Real.sqrt b), y⁻¹ := by`. Rewrite using `[integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc, Set.inter_eq_left.mpr (show Icc (Real.sqrt a) (Real.sqrt b) ⊆ Ioi 0 from fun y hy => hsa.trans_le hy.1)]`.

Use `_ = Real.log (Real.sqrt b / Real.sqrt a) := by`. Rewrite using `[integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hsab, integral_inv_of_pos hsa hsb]`. Use `_ = Real.log (b / a) / 2 := by`. Rewrite using `[Real.log_div hsb.ne' hsa.ne', Real.log_sqrt hb.le, Real.log_sqrt ha.le, Real.log_div hb.ne' ha.ne']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem polar_radial (n : ℕ) (hn : 1 ≤ n) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∫ y in Ioi (0:ℝ), y ^ (2 * n - 1) •
        (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) y =
      Real.log (b / a) / 2 := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hb : 0 < b := ha.trans_le hab
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsab : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt hab
  have hpt : ∀ y : ℝ, y ^ (2 * n - 1) •
      (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) y =
        (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => t⁻¹) y := by
    intro y
    classical
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hy : y ∈ Icc (Real.sqrt a) (Real.sqrt b)
    · rw [if_pos hy, if_pos hy]
      have hy0 : 0 < y := hsa.trans_le hy.1
      rw [smul_eq_mul, Real.rpow_neg (by positivity), Real.rpow_natCast]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
      have hsplit : (y ^ 2) ^ (k + 1) = y ^ (2 * k + 1) * y := by ring
      rw [hsplit, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hy0.ne'), one_mul]
    · rw [if_neg hy, if_neg hy, smul_zero]
  calc ∫ y in Ioi (0:ℝ), y ^ (2 * n - 1) •
        (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) y
      = ∫ y in Ioi (0:ℝ), (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => t⁻¹) y := by
        exact congrArg _ (funext hpt)
    _ = ∫ y in Icc (Real.sqrt a) (Real.sqrt b), y⁻¹ := by
        rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
          Set.inter_eq_left.mpr (show Icc (Real.sqrt a) (Real.sqrt b) ⊆ Ioi 0 from
            fun y hy => hsa.trans_le hy.1)]
    _ = Real.log (Real.sqrt b / Real.sqrt a) := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hsab,
          integral_inv_of_pos hsa hsb]
    _ = Real.log (b / a) / 2 := by
        rw [Real.log_div hsb.ne' hsa.ne', Real.log_sqrt hb.le, Real.log_sqrt ha.le,
          Real.log_div hb.ne' ha.ne']
        ring

/- English proof (translation)
Introduce `hn a b ha hab`. Use `nontrivial_V_of_one_le n hn` as an intermediate fact. Establish `hb : 0 < b` using `ha.trans_le hab`. Establish `hsa0` using `Real.sqrt_nonneg a`. Establish `hsb0` using `Real.sqrt_nonneg b`.

Establish `hsa : Real.sqrt a ^ 2 = a` using `Real.sq_sqrt ha.le`. Establish `hsb : Real.sqrt b ^ 2 = b` using `Real.sq_sqrt hb.le`. Establish `hmem : ∀ y : ReciprocityTheory.L2DbarEstimates.V n, (a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b) ↔ (Real.sqrt a ≤ ‖y‖ ∧ ‖y‖ ≤ Real.sqrt b)`. Introduce `y`. Establish `h0` using `norm_nonneg y`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨by nlinarith, by nlinarith⟩`. Establish `hSc : IsClosed {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}`. Establish `h1 : IsClosed {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2}` using `isClosed_le continuous_const (continuous_norm.pow 2)`. Establish `h2 : IsClosed {y : ReciprocityTheory.L2DbarEstimates.V n | ‖y‖ ^ 2 ≤ b}` using `isClosed_le (continuous_norm.pow 2) continuous_const`.

Conclude with `h1.inter h2`. Establish `hsub : {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} ⊆ closedBall 0 (b + 1)`. Introduce `y hy`. Rewrite using `[mem_closedBall, dist_zero_right]`. Establish `h0` using `norm_nonneg y`.

Establish `h2 : ‖y‖ ^ 2 ≤ b` using `hy.2`. Use polynomial arithmetic with `[mul_self_nonneg (‖y‖ - 1)]`. Establish `hK : IsCompact {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}` using `(isCompact_closedBall (0 : ReciprocityTheory.L2DbarEstimates.V n) (b + 1)).of_isClosed_subset hSc hsub`. Establish `hcont : ContinuousOn (fun y : ReciprocityTheory.L2DbarEstimates.V n => (‖y‖ ^ 2) ^ (-(n : ℝ))) {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}` using `(continuous_norm.pow 2).continuousOn.rpow_const (fun y hy => Or.inl (ha.trans_le (hy : a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b).1).ne')`. Establish `hint_r : IntegrableOn (fun y : ReciprocityTheory.L2DbarEstimates.V n => (‖y‖ ^ 2) ^ (-(n : ℝ))) {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} volume` using `hcont.integrableOn_compact hK`.

Establish `hnn : 0 ≤ᵐ[volume.restrict {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}] (fun y : ReciprocityTheory.L2DbarEstimates.V n => (‖y‖ ^ 2) ^ (-(n : ℝ)))` using `ae_of_all _ (fun y => Real.rpow_nonneg (by positivity) _)`. Rewrite using `[← ofReal_integral_eq_lintegral_ofReal hint_r hnn]`. Use `congr 1`. Establish `hpt : ∀ y : ReciprocityTheory.L2DbarEstimates.V n, {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}.indicator (fun y : ReciprocityTheory.L2DbarEstimates.V n => (‖y‖ ^ 2) ^ (-(n : ℝ))) y = (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ ( …`. Introduce `y`.

Rewrite using `[Set.indicator_apply, Set.indicator_apply]`. Distinguish the cases in `hy : y ∈ {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}`. Rewrite using `[if_pos hy, if_pos (show ‖y‖ ∈ Icc (Real.sqrt a) (Real.sqrt b) from (hmem y).1 hy)]`. Rewrite using `[if_neg hy, if_neg (show ‖y‖ ∉ Icc (Real.sqrt a) (Real.sqrt b) from fun h => hy ((hmem y).2 h))]`. Establish `hI : ∫ y in {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}, (‖y‖ ^ 2) ^ (-(n : ℝ)) = ∫ y : ReciprocityTheory.L2DbarEstimates.V n, (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) ‖y‖`.

Rewrite using `[← integral_indicator hSc.measurableSet]`. Conclude with `congrArg _ (funext hpt)`. Establish `hP : ∫ y : ReciprocityTheory.L2DbarEstimates.V n, (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) ‖y‖ = (2 * n : ℕ) • (volume : Measure (ReciprocityTheory.L2DbarEstimates.V n)).real (ball 0 1) • ∫ y in Ioi (0:ℝ), y ^ (2 * n - 1) • (Icc (Real.sqrt a …`. Rewrite using `[integral_fun_norm_addHaar (volume : Measure (ReciprocityTheory.L2DbarEstimates.V n)), polar_finrank]`. Rewrite using `[hI, hP, polar_ballReal n hn, polar_radial n hn a b ha hab, nsmul_eq_mul, smul_eq_mul]`.

Take `⟨k, rfl⟩ : ∃ k, n = k + 1` from `⟨n - 1, by omega⟩`. Rewrite using `[Nat.add_sub_cancel, Nat.factorial_succ]`. Use `push_cast`. Establish `hk : (k.factorial : ℝ) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)`. Clear the denominators using the available nonvanishing facts.
-/
theorem polar (n : ℕ) : PolarStatement n := by
  intro hn a b ha hab
  have := nontrivial_V_of_one_le n hn
  have hb : 0 < b := ha.trans_le hab
  have hsa0 := Real.sqrt_nonneg a
  have hsb0 := Real.sqrt_nonneg b
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
  have hmem : ∀ y : ReciprocityTheory.L2DbarEstimates.V n, (a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b) ↔
      (Real.sqrt a ≤ ‖y‖ ∧ ‖y‖ ≤ Real.sqrt b) := by
    intro y
    have h0 := norm_nonneg y
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · calc Real.sqrt a ≤ Real.sqrt (‖y‖ ^ 2) := Real.sqrt_le_sqrt h1
          _ = ‖y‖ := Real.sqrt_sq h0
      · calc ‖y‖ = Real.sqrt (‖y‖ ^ 2) := (Real.sqrt_sq h0).symm
          _ ≤ Real.sqrt b := Real.sqrt_le_sqrt h2
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
  have hSc : IsClosed {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} := by
    have h1 : IsClosed {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2} :=
      isClosed_le continuous_const (continuous_norm.pow 2)
    have h2 : IsClosed {y : ReciprocityTheory.L2DbarEstimates.V n | ‖y‖ ^ 2 ≤ b} :=
      isClosed_le (continuous_norm.pow 2) continuous_const
    exact h1.inter h2
  have hsub : {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} ⊆ closedBall 0 (b + 1) := by
    intro y hy
    rw [mem_closedBall, dist_zero_right]
    have h0 := norm_nonneg y
    have h2 : ‖y‖ ^ 2 ≤ b := hy.2
    nlinarith [mul_self_nonneg (‖y‖ - 1)]
  have hK : IsCompact {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} :=
    (isCompact_closedBall (0 : ReciprocityTheory.L2DbarEstimates.V n) (b + 1)).of_isClosed_subset hSc hsub
  have hcont : ContinuousOn (fun y : ReciprocityTheory.L2DbarEstimates.V n => (‖y‖ ^ 2) ^ (-(n : ℝ)))
      {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} :=
    (continuous_norm.pow 2).continuousOn.rpow_const
      (fun y hy => Or.inl (ha.trans_le (hy : a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b).1).ne')
  have hint_r : IntegrableOn (fun y : ReciprocityTheory.L2DbarEstimates.V n => (‖y‖ ^ 2) ^ (-(n : ℝ)))
      {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} volume :=
    hcont.integrableOn_compact hK
  have hnn : 0 ≤ᵐ[volume.restrict {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}]
      (fun y : ReciprocityTheory.L2DbarEstimates.V n => (‖y‖ ^ 2) ^ (-(n : ℝ))) :=
    ae_of_all _ (fun y => Real.rpow_nonneg (by positivity) _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint_r hnn]
  congr 1
  have hpt : ∀ y : ReciprocityTheory.L2DbarEstimates.V n,
      {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}.indicator
          (fun y : ReciprocityTheory.L2DbarEstimates.V n => (‖y‖ ^ 2) ^ (-(n : ℝ))) y =
        (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) ‖y‖ := by
    intro y
    classical
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hy : y ∈ {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}
    · rw [if_pos hy, if_pos (show ‖y‖ ∈ Icc (Real.sqrt a) (Real.sqrt b) from (hmem y).1 hy)]
    · rw [if_neg hy, if_neg (show ‖y‖ ∉ Icc (Real.sqrt a) (Real.sqrt b) from
        fun h => hy ((hmem y).2 h))]
  have hI : ∫ y in {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}, (‖y‖ ^ 2) ^ (-(n : ℝ)) =
      ∫ y : ReciprocityTheory.L2DbarEstimates.V n, (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) ‖y‖ := by
    rw [← integral_indicator hSc.measurableSet]
    exact congrArg _ (funext hpt)
  have hP : ∫ y : ReciprocityTheory.L2DbarEstimates.V n, (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) ‖y‖ =
      (2 * n : ℕ) • (volume : Measure (ReciprocityTheory.L2DbarEstimates.V n)).real (ball 0 1) • ∫ y in Ioi (0:ℝ),
        y ^ (2 * n - 1) • (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) y := by
    rw [integral_fun_norm_addHaar (volume : Measure (ReciprocityTheory.L2DbarEstimates.V n)), polar_finrank]
  rw [hI, hP, polar_ballReal n hn, polar_radial n hn a b ha hab,
    nsmul_eq_mul, smul_eq_mul]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  field_simp

end ReciprocityTheory.L2DbarEstimates.I

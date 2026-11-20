import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.RiemHaarOfSteps

noncomputable section

namespace PI.IwaMeasEx.Gauge.ZetaZeros

open Filter Topology Formalism.MainNotions.S

section Trotter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

/- English proof (translation)
Establish `h1 : HasSum (fun i : ℕ => ((i.factorial : ℝ)⁻¹) • x ^ i) (NormedSpace.exp x)` using `NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x`. Establish `h2 : HasSum (fun i : ℕ => ((i.factorial : ℝ)⁻¹) • ‖x‖ ^ i) (Real.exp ‖x‖)`. Rewrite using `[Real.exp_eq_exp_ℝ]`. Conclude with `NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖`. Establish `h1'` using `(hasSum_nat_add_iff' m).mpr h1`.

Establish `h2'` using `(hasSum_nat_add_iff' m).mpr h2`. Simplify using `only [smul_eq_mul] at h2'`. Use `h1'.norm_le_of_bounded h2' (fun i => ?_)` and prove the remaining obligations. Rewrite using `[norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]`. Conclude with `mul_le_mul_of_nonneg_left (norm_pow_le x _) (by positivity)`.
-/
theorem norm_exp_sub_partial_le (x : 𝔸) (m : ℕ) :
    ‖NormedSpace.exp x - ∑ i ∈ Finset.range m, ((i.factorial : ℝ)⁻¹) • x ^ i‖ ≤
      Real.exp ‖x‖ - ∑ i ∈ Finset.range m, ((i.factorial : ℝ)⁻¹) * ‖x‖ ^ i := by
  have h1 : HasSum (fun i : ℕ => ((i.factorial : ℝ)⁻¹) • x ^ i) (NormedSpace.exp x) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x
  have h2 : HasSum (fun i : ℕ => ((i.factorial : ℝ)⁻¹) • ‖x‖ ^ i) (Real.exp ‖x‖) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖
  have h1' := (hasSum_nat_add_iff' m).mpr h1
  have h2' := (hasSum_nat_add_iff' m).mpr h2
  simp only [smul_eq_mul] at h2'
  refine h1'.norm_le_of_bounded h2' (fun i => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_pow_le x _) (by positivity)

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Establish `hb : ∀ z : 𝔸, z ∈ Metric.eball (0 : 𝔸) (NormedSpace.expSeries ℝ 𝔸).radius`. Introduce `z`.

Rewrite using `[NormedSpace.expSeries_radius_eq_top]`. Conclude with `edist_lt_top _ _`. Rewrite using `[pow_succ, ih, succ_nsmul, NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) ((Commute.refl c).smul_left j) (hb _) (hb _)]`.
-/
theorem exp_pow_eqA (c : 𝔸) (j : ℕ) : NormedSpace.exp c ^ j = NormedSpace.exp (j • c) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hb : ∀ z : 𝔸, z ∈ Metric.eball (0 : 𝔸) (NormedSpace.expSeries ℝ 𝔸).radius := by
      intro z
      rw [NormedSpace.expSeries_radius_eq_top]
      exact edist_lt_top _ _
    rw [pow_succ, ih, succ_nsmul,
      NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) ((Commute.refl c).smul_left j) (hb _) (hb _)]

/- English proof (translation)
Simplify using `using norm_exp_sub_partial_le x 0`.
-/
theorem norm_exp_le' (x : 𝔸) : ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  simpa using norm_exp_sub_partial_le x 0

/- English proof (translation)
Establish `e1 : ∑ i ∈ Finset.range 1, ((i.factorial : ℝ)⁻¹) • x ^ i = 1` using `by simp`. Establish `e2 : ∑ i ∈ Finset.range 1, ((i.factorial : ℝ)⁻¹) * ‖x‖ ^ i = 1` using `by simp`. Establish `key` using `norm_exp_sub_partial_le x 1`. Rewrite `key` using `[e1, e2]`. Establish `hr` using `Real.abs_exp_sub_one_le (x := ‖x‖) (by rwa [abs_of_nonneg (norm_nonneg x)])`.

Rewrite `hr` using `[abs_of_nonneg (norm_nonneg x), abs_le]`. Combine the linear relations using `[hr.2]`.
-/
theorem norm_exp_sub_one_le' (x : 𝔸) (hx : ‖x‖ ≤ 1) : ‖NormedSpace.exp x - 1‖ ≤ 2 * ‖x‖ := by
  have e1 : ∑ i ∈ Finset.range 1, ((i.factorial : ℝ)⁻¹) • x ^ i = 1 := by simp
  have e2 : ∑ i ∈ Finset.range 1, ((i.factorial : ℝ)⁻¹) * ‖x‖ ^ i = 1 := by simp
  have key := norm_exp_sub_partial_le x 1
  rw [e1, e2] at key
  have hr := Real.abs_exp_sub_one_le (x := ‖x‖) (by rwa [abs_of_nonneg (norm_nonneg x)])
  rw [abs_of_nonneg (norm_nonneg x), abs_le] at hr
  linarith [hr.2]

/- English proof (translation)
Establish `e1 : ∑ i ∈ Finset.range 2, ((i.factorial : ℝ)⁻¹) • x ^ i = 1 + x` using `by simp [Finset.sum_range_succ]`. Establish `e2 : ∑ i ∈ Finset.range 2, ((i.factorial : ℝ)⁻¹) * ‖x‖ ^ i = 1 + ‖x‖` using `by simp [Finset.sum_range_succ]`. Establish `key` using `norm_exp_sub_partial_le x 2`. Rewrite `key` using `[e1, e2]`. Establish `hr` using `Real.abs_exp_sub_one_sub_id_le (x := ‖x‖) (by rwa [abs_of_nonneg (norm_nonneg x)])`.

Rewrite `hr` using `[abs_le]`. Rewrite using `[sub_sub]`. Combine the linear relations using `[hr.2]`.
-/
theorem norm_exp_sub_one_sub_le' (x : 𝔸) (hx : ‖x‖ ≤ 1) : ‖NormedSpace.exp x - 1 - x‖ ≤ ‖x‖ ^ 2 := by
  have e1 : ∑ i ∈ Finset.range 2, ((i.factorial : ℝ)⁻¹) • x ^ i = 1 + x := by simp [Finset.sum_range_succ]
  have e2 : ∑ i ∈ Finset.range 2, ((i.factorial : ℝ)⁻¹) * ‖x‖ ^ i = 1 + ‖x‖ := by simp [Finset.sum_range_succ]
  have key := norm_exp_sub_partial_le x 2
  rw [e1, e2] at key
  have hr := Real.abs_exp_sub_one_sub_id_le (x := ‖x‖) (by rwa [abs_of_nonneg (norm_nonneg x)])
  rw [abs_le] at hr
  rw [sub_sub]
  linarith [hr.2]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `e : S ^ (k + 1 + 1) - T ^ (k + 1 + 1) = S * (S ^ (k + 1) - T ^ (k + 1)) + (S - T) * T ^ (k + 1)`. Rewrite using `[pow_succ' S (k + 1), pow_succ' T (k + 1)]`.

Simplify using `only [mul_sub, sub_mul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Establish `hTk : ‖T ^ (k + 1)‖ ≤ M ^ (k + 1)` using `(norm_pow_le T _).trans (pow_le_pow_left₀ (norm_nonneg _) hT _)`. Establish `hD0 : 0 ≤ ‖S - T‖` using `norm_nonneg _`.

Establish `hMk : 0 ≤ M ^ k` using `pow_nonneg hM k`. Establish `i1 : ‖S * (S ^ (k + 1) - T ^ (k + 1))‖ ≤ M * (((k : ℝ) + 1) * M ^ k * ‖S - T‖)` using `(norm_mul_le _ _).trans (mul_le_mul hS ih (norm_nonneg _) hM)`. Establish `i2 : ‖(S - T) * T ^ (k + 1)‖ ≤ ‖S - T‖ * M ^ (k + 1)` using `(norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hTk hD0)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_pow_sub_pow_le' (S T : 𝔸) {M : ℝ} (hM : 0 ≤ M) (hS : ‖S‖ ≤ M) (hT : ‖T‖ ≤ M) (k : ℕ) :
    ‖S ^ (k + 1) - T ^ (k + 1)‖ ≤ ((k : ℝ) + 1) * M ^ k * ‖S - T‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : S ^ (k + 1 + 1) - T ^ (k + 1 + 1) =
        S * (S ^ (k + 1) - T ^ (k + 1)) + (S - T) * T ^ (k + 1) := by
      rw [pow_succ' S (k + 1), pow_succ' T (k + 1)]
      simp only [mul_sub, sub_mul]
      abel
    rw [e]
    have hTk : ‖T ^ (k + 1)‖ ≤ M ^ (k + 1) :=
      (norm_pow_le T _).trans (pow_le_pow_left₀ (norm_nonneg _) hT _)
    have hD0 : 0 ≤ ‖S - T‖ := norm_nonneg _
    have hMk : 0 ≤ M ^ k := pow_nonneg hM k
    have i1 : ‖S * (S ^ (k + 1) - T ^ (k + 1))‖ ≤ M * (((k : ℝ) + 1) * M ^ k * ‖S - T‖) :=
      (norm_mul_le _ _).trans (mul_le_mul hS ih (norm_nonneg _) hM)
    have i2 : ‖(S - T) * T ^ (k + 1)‖ ≤ ‖S - T‖ * M ^ (k + 1) :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hTk hD0)
    calc ‖S * (S ^ (k + 1) - T ^ (k + 1)) + (S - T) * T ^ (k + 1)‖
        ≤ M * (((k : ℝ) + 1) * M ^ k * ‖S - T‖) + ‖S - T‖ * M ^ (k + 1) :=
          (norm_add_le _ _).trans (add_le_add i1 i2)
      _ = (((k + 1 : ℕ) : ℝ) + 1) * M ^ (k + 1) * ‖S - T‖ := by push_cast; ring

/- English proof (translation)
Use `set r := ‖A‖ + ‖B‖ with hr`. Establish `hr0 : 0 ≤ r` using `by positivity`. Rewrite using `[tendsto_iff_norm_sub_tendsto_zero]`. Establish `hC : Tendsto (fun k : ℕ => 7 * r ^ 2 * Real.exp r / (k : ℝ)) atTop (𝓝 0)` using `tendsto_const_div_atTop_nhds_zero_nat _`. Use `squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hC` and prove the remaining obligations.

Take `⟨N, hN⟩` from `exists_nat_gt (2 * r)`. Use `filter_upwards [eventually_ge_atTop (N + 1)] with k hk`. Take `⟨m, rfl⟩ : ∃ m, k = m + 1` from `⟨k - 1, by omega⟩`. Establish `hkc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1` using `by push_cast; ring`. Establish `hkpos : (0 : ℝ) < (m : ℝ) + 1` using `by positivity`.

Establish `hN' : ((N : ℝ) + 1) ≤ (m : ℝ) + 1` using `by exact_mod_cast hk`. Establish `hk2 : 2 * r < (m : ℝ) + 1` using `by linarith`. Rewrite using `[hkc]`. Use `set κ : ℝ := (m : ℝ) + 1 with hκ`. Use `set a := κ⁻¹ • A with ha_def`.

Use `set b := κ⁻¹ • B with hb_def`. Use `set ρ := κ⁻¹ * r with hρ`. Establish `hρ0 : 0 ≤ ρ` using `by positivity`. Establish `hρ1 : ρ ≤ 1`. Rewrite using `[hρ, inv_mul_le_iff₀ hkpos]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hna : ‖a‖ = κ⁻¹ * ‖A‖`. Rewrite using `[ha_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hkpos]`. Establish `hnb : ‖b‖ = κ⁻¹ * ‖B‖`. Rewrite using `[hb_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hkpos]`.

Establish `hsum : ‖a‖ + ‖b‖ = ρ` using `by rw [hna, hnb, hρ, hr]; ring`. Establish `haρ : ‖a‖ ≤ ρ` using `by linarith [norm_nonneg b]`. Establish `hbρ : ‖b‖ ≤ ρ` using `by linarith [norm_nonneg a]`. Establish `habρ : ‖a + b‖ ≤ ρ` using `(norm_add_le a b).trans hsum.le`. Establish `ha1 : ‖a‖ ≤ 1` using `haρ.trans hρ1`.

Establish `hb1 : ‖b‖ ≤ 1` using `hbρ.trans hρ1`. Establish `hab1 : ‖a + b‖ ≤ 1` using `habρ.trans hρ1`. Establish `hid : NormedSpace.exp a * NormedSpace.exp b - NormedSpace.exp (a + b) = (NormedSpace.exp b - 1 - b) + a * (NormedSpace.exp b - 1) + (NormedSpace.exp a - 1 - a) * NormedSpace.exp b - (NormedSpace.exp (a + b) - 1 - (a + b))` using `by noncomm_ring`. Establish `q1 : ‖NormedSpace.exp b - 1 - b‖ ≤ ρ ^ 2` using `(norm_exp_sub_one_sub_le' b hb1).trans (pow_le_pow_left₀ (norm_nonneg _) hbρ 2)`. Establish `q2 : ‖a * (NormedSpace.exp b - 1)‖ ≤ ρ * (2 * ρ)` using `(norm_mul_le _ _).trans (mul_le_mul haρ ((norm_exp_sub_one_le' b hb1).trans (by linarith)) (norm_nonneg _) hρ0)`.

Establish `hexpb : ‖NormedSpace.exp b‖ ≤ 3` using `(norm_exp_le' b).trans ((Real.exp_le_exp.mpr hb1).trans ((Real.exp_one_lt_d9).le.trans (by norm_num)))`. Establish `q3 : ‖(NormedSpace.exp a - 1 - a) * NormedSpace.exp b‖ ≤ ρ ^ 2 * 3` using `(norm_mul_le _ _).trans (mul_le_mul ((norm_exp_sub_one_sub_le' a ha1).trans (pow_le_pow_left₀ (norm_nonneg _) haρ 2)) hexpb (norm_nonneg _) (by positivity))`. Establish `q4 : ‖NormedSpace.exp (a + b) - 1 - (a + b)‖ ≤ ρ ^ 2` using `(norm_exp_sub_one_sub_le' (a + b) hab1).trans (pow_le_pow_left₀ (norm_nonneg _) habρ 2)`. Establish `hD : ‖NormedSpace.exp a * NormedSpace.exp b - NormedSpace.exp (a + b)‖ ≤ 7 * ρ ^ 2`. Rewrite using `[hid]`.

Use `norm_sub_le ((NormedSpace.exp b - 1 - b) + a * (NormedSpace.exp b - 1) + (NormedSpace.exp a - 1 - a) * NormedSpace.exp b) (NormedSpace.exp (a + b) - 1 - (a + b))` as an intermediate fact. Use `norm_add_le ((NormedSpace.exp b - 1 - b) + a * (NormedSpace.exp b - 1)) ((NormedSpace.exp a - 1 - a) * NormedSpace.exp b)` as an intermediate fact. Use `norm_add_le (NormedSpace.exp b - 1 - b) (a * (NormedSpace.exp b - 1))` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Use `set M := Real.exp ρ with hMdef`.

Establish `hM0 : 0 ≤ M` using `(Real.exp_pos _).le`. Establish `hS : ‖NormedSpace.exp a * NormedSpace.exp b‖ ≤ M`. Use `(norm_mul_le _ _).trans ?_` and prove the remaining obligations. Use `mul_le_mul (norm_exp_le' a) (norm_exp_le' b) (norm_nonneg _) (Real.exp_pos _).le` as an intermediate fact. Rewrite `this` using `[← Real.exp_add, hsum]`.

Conclude with `this`. Establish `hT : ‖NormedSpace.exp (a + b)‖ ≤ M` using `(norm_exp_le' _).trans (Real.exp_le_exp.mpr habρ)`. Establish `hTk : NormedSpace.exp (a + b) ^ (m + 1) = NormedSpace.exp (A + B)`. Rewrite using `[exp_pow_eqA, ha_def, hb_def, ← smul_add, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hkc, mul_inv_cancel₀ hkpos.ne', one_smul]`. Establish `hmain` using `norm_pow_sub_pow_le' _ _ hM0 hS hT m`.

Rewrite `hmain` using `[hTk]`. Establish `hMm : M ^ m ≤ Real.exp r`. Rewrite using `[hMdef, ← Real.exp_nat_mul]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Rewrite using `[hρ, ← mul_assoc]`.

Establish `: (m : ℝ) * κ⁻¹ ≤ 1`. Rewrite using `[mul_inv_le_iff₀ hkpos]`. Combine the linear equalities and inequalities to obtain the conclusion. Use the polynomial consequences of the given equalities and inequalities. Establish `hfin : ((m : ℝ) + 1) * M ^ m * ‖NormedSpace.exp a * NormedSpace.exp b - NormedSpace.exp (a + b)‖ ≤ 7 * r ^ 2 * Real.exp r / κ`.

Establish `h1 : ((m : ℝ) + 1) * M ^ m * ‖NormedSpace.exp a * NormedSpace.exp b - NormedSpace.exp (a + b)‖ ≤ κ * Real.exp r * (7 * ρ ^ 2)`. Apply `mul_le_mul (mul_le_mul_of_nonneg_left hMm hkpos.le) hD (norm_nonneg _)` to reduce the goal to its premises. Check the signs of the components of the expression. Establish `h2 : κ * Real.exp r * (7 * ρ ^ 2) = 7 * r ^ 2 * Real.exp r / κ`. Rewrite using `[hρ]`.

Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `hmain.trans hfin`.
-/
theorem trotter (A B : 𝔸) :
    Tendsto (fun k : ℕ => (NormedSpace.exp ((k : ℝ)⁻¹ • A) * NormedSpace.exp ((k : ℝ)⁻¹ • B)) ^ k) atTop
      (𝓝 (NormedSpace.exp (A + B))) := by
  set r := ‖A‖ + ‖B‖ with hr
  have hr0 : 0 ≤ r := by positivity
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hC : Tendsto (fun k : ℕ => 7 * r ^ 2 * Real.exp r / (k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hC
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * r)
  filter_upwards [eventually_ge_atTop (N + 1)] with k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hkc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  have hkpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hN' : ((N : ℝ) + 1) ≤ (m : ℝ) + 1 := by exact_mod_cast hk
  have hk2 : 2 * r < (m : ℝ) + 1 := by linarith
  rw [hkc]
  set κ : ℝ := (m : ℝ) + 1 with hκ
  set a := κ⁻¹ • A with ha_def
  set b := κ⁻¹ • B with hb_def
  set ρ := κ⁻¹ * r with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 := by
    rw [hρ, inv_mul_le_iff₀ hkpos]
    linarith
  have hna : ‖a‖ = κ⁻¹ * ‖A‖ := by
    rw [ha_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hkpos]
  have hnb : ‖b‖ = κ⁻¹ * ‖B‖ := by
    rw [hb_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hkpos]
  have hsum : ‖a‖ + ‖b‖ = ρ := by rw [hna, hnb, hρ, hr]; ring
  have haρ : ‖a‖ ≤ ρ := by linarith [norm_nonneg b]
  have hbρ : ‖b‖ ≤ ρ := by linarith [norm_nonneg a]
  have habρ : ‖a + b‖ ≤ ρ := (norm_add_le a b).trans hsum.le
  have ha1 : ‖a‖ ≤ 1 := haρ.trans hρ1
  have hb1 : ‖b‖ ≤ 1 := hbρ.trans hρ1
  have hab1 : ‖a + b‖ ≤ 1 := habρ.trans hρ1

  have hid : NormedSpace.exp a * NormedSpace.exp b - NormedSpace.exp (a + b) =
      (NormedSpace.exp b - 1 - b) + a * (NormedSpace.exp b - 1) + (NormedSpace.exp a - 1 - a) * NormedSpace.exp b -
        (NormedSpace.exp (a + b) - 1 - (a + b)) := by
    noncomm_ring
  have q1 : ‖NormedSpace.exp b - 1 - b‖ ≤ ρ ^ 2 :=
    (norm_exp_sub_one_sub_le' b hb1).trans (pow_le_pow_left₀ (norm_nonneg _) hbρ 2)
  have q2 : ‖a * (NormedSpace.exp b - 1)‖ ≤ ρ * (2 * ρ) :=
    (norm_mul_le _ _).trans (mul_le_mul haρ ((norm_exp_sub_one_le' b hb1).trans (by linarith))
      (norm_nonneg _) hρ0)
  have hexpb : ‖NormedSpace.exp b‖ ≤ 3 :=
    (norm_exp_le' b).trans ((Real.exp_le_exp.mpr hb1).trans
      ((Real.exp_one_lt_d9).le.trans (by norm_num)))
  have q3 : ‖(NormedSpace.exp a - 1 - a) * NormedSpace.exp b‖ ≤ ρ ^ 2 * 3 :=
    (norm_mul_le _ _).trans (mul_le_mul ((norm_exp_sub_one_sub_le' a ha1).trans
      (pow_le_pow_left₀ (norm_nonneg _) haρ 2)) hexpb (norm_nonneg _) (by positivity))
  have q4 : ‖NormedSpace.exp (a + b) - 1 - (a + b)‖ ≤ ρ ^ 2 :=
    (norm_exp_sub_one_sub_le' (a + b) hab1).trans (pow_le_pow_left₀ (norm_nonneg _) habρ 2)
  have hD : ‖NormedSpace.exp a * NormedSpace.exp b - NormedSpace.exp (a + b)‖ ≤ 7 * ρ ^ 2 := by
    rw [hid]
    have := norm_sub_le ((NormedSpace.exp b - 1 - b) + a * (NormedSpace.exp b - 1) +
      (NormedSpace.exp a - 1 - a) * NormedSpace.exp b) (NormedSpace.exp (a + b) - 1 - (a + b))
    have := norm_add_le ((NormedSpace.exp b - 1 - b) + a * (NormedSpace.exp b - 1))
      ((NormedSpace.exp a - 1 - a) * NormedSpace.exp b)
    have := norm_add_le (NormedSpace.exp b - 1 - b) (a * (NormedSpace.exp b - 1))
    nlinarith

  set M := Real.exp ρ with hMdef
  have hM0 : 0 ≤ M := (Real.exp_pos _).le
  have hS : ‖NormedSpace.exp a * NormedSpace.exp b‖ ≤ M := by
    refine (norm_mul_le _ _).trans ?_
    have := mul_le_mul (norm_exp_le' a) (norm_exp_le' b) (norm_nonneg _) (Real.exp_pos _).le
    rw [← Real.exp_add, hsum] at this
    exact this
  have hT : ‖NormedSpace.exp (a + b)‖ ≤ M := (norm_exp_le' _).trans (Real.exp_le_exp.mpr habρ)
  have hTk : NormedSpace.exp (a + b) ^ (m + 1) = NormedSpace.exp (A + B) := by
    rw [exp_pow_eqA, ha_def, hb_def, ← smul_add, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hkc,
      mul_inv_cancel₀ hkpos.ne', one_smul]
  have hmain := norm_pow_sub_pow_le' _ _ hM0 hS hT m
  rw [hTk] at hmain
  have hMm : M ^ m ≤ Real.exp r := by
    rw [hMdef, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    rw [hρ, ← mul_assoc]
    have : (m : ℝ) * κ⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ hkpos]
      linarith
    nlinarith
  have hfin : ((m : ℝ) + 1) * M ^ m * ‖NormedSpace.exp a * NormedSpace.exp b - NormedSpace.exp (a + b)‖ ≤
      7 * r ^ 2 * Real.exp r / κ := by
    have h1 : ((m : ℝ) + 1) * M ^ m * ‖NormedSpace.exp a * NormedSpace.exp b - NormedSpace.exp (a + b)‖ ≤
        κ * Real.exp r * (7 * ρ ^ 2) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hMm hkpos.le) hD (norm_nonneg _)
      positivity
    have h2 : κ * Real.exp r * (7 * ρ ^ 2) = 7 * r ^ 2 * Real.exp r / κ := by
      rw [hρ]
      field_simp
    linarith
  exact hmain.trans hfin

end Trotter

section Mat

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/- English proof (translation)
Rewrite using `[Matrix.linfty_opNorm_def]`. Establish `h1 : ‖A i j‖₊ ≤ ∑ k, ‖A i k‖₊` using `Finset.single_le_sum (f := fun k => ‖A i k‖₊) (fun _ _ => zero_le) (Finset.mem_univ j)`. Establish `h2 : ∑ k, ‖A i k‖₊ ≤ (Finset.univ : Finset (Fin n)).sup fun i => ∑ k, ‖A i k‖₊` using `Finset.le_sup (f := fun i => ∑ k, ‖A i k‖₊) (Finset.mem_univ i)`. Conclude with `h1.trans h2` after adjusting the coercions.
-/
theorem entry_le_linftyA {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖A i j‖ ≤ ‖A‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h1 : ‖A i j‖₊ ≤ ∑ k, ‖A i k‖₊ :=
    Finset.single_le_sum (f := fun k => ‖A i k‖₊) (fun _ _ => zero_le) (Finset.mem_univ j)
  have h2 : ∑ k, ‖A i k‖₊ ≤ (Finset.univ : Finset (Fin n)).sup fun i => ∑ k, ‖A i k‖₊ :=
    Finset.le_sup (f := fun i => ∑ k, ‖A i k‖₊) (Finset.mem_univ i)
  exact_mod_cast h1.trans h2

/- English proof (translation)
Establish `: Nonempty (Fin n)` using `⟨i⟩`. Establish `: CompleteSpace (Matrix (Fin n) (Fin n) ℂ)` using `FiniteDimensional.complete ℝ _`. Establish `h` using `trotter (𝔸 := Matrix (Fin n) (Fin n) ℂ) A B`. Rewrite `h` using `[tendsto_iff_norm_sub_tendsto_zero]`. Rewrite using `[tendsto_iff_norm_sub_tendsto_zero]`.

Use `squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) h` and prove the remaining obligations. Rewrite using `[← Matrix.sub_apply]`. Conclude with `entry_le_linftyA _ i j`.
-/
theorem trotter_entry {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    Tendsto (fun k : ℕ => ((NormedSpace.exp ((k : ℝ)⁻¹ • A) * NormedSpace.exp ((k : ℝ)⁻¹ • B)) ^ k) i j)
      atTop (𝓝 (NormedSpace.exp (A + B) i j)) := by
  have : Nonempty (Fin n) := ⟨i⟩
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h := trotter (𝔸 := Matrix (Fin n) (Fin n) ℂ) A B
  rw [tendsto_iff_norm_sub_tendsto_zero] at h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) h
  rw [← Matrix.sub_apply]
  exact entry_le_linftyA _ i j

end Mat

/- English proof (translation)
The claim follows from `tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => trotter_entry A B i j`.
-/
theorem trotter_mat {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (fun k : ℕ => (NormedSpace.exp ((k : ℝ)⁻¹ • A) * NormedSpace.exp ((k : ℝ)⁻¹ • B)) ^ k) atTop
      (𝓝 (NormedSpace.exp (A + B))) :=
  tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => trotter_entry A B i j

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rfl`. Consider the case `succ k ih`. Rewrite using `[pow_succ, pow_succ, ← ih]`. Both sides reduce to the same expression.
-/
theorem uMat_powA {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (k : ℕ) : uMat (g ^ k) = uMat g ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, pow_succ, ← ih]
    rfl

/- English proof (translation)
Introduce `n ε K hK X hX Y hY t`. Establish `hX' : ∀ s : ℝ, ∃ h ∈ K, uMat h = NormedSpace.exp ((s : ℂ) • X)` using `hX`. Establish `hY' : ∀ s : ℝ, ∃ h ∈ K, uMat h = NormedSpace.exp ((s : ℂ) • Y)` using `hY`. Use `choose h1 hh1 e1 using fun k : ℕ => hX' (t / k)`. Use `choose h2 hh2 e2 using fun k : ℕ => hY' (t / k)`.

Establish `hs : ∀ (k : ℕ) (Z : Matrix (Fin n) (Fin n) ℂ), ((t / k : ℝ) : ℂ) • Z = (k : ℝ)⁻¹ • ((t : ℂ) • Z)`. Introduce `k Z`. Rewrite using `[← smul_assoc, Complex.real_smul, ← Complex.ofReal_mul, inv_mul_eq_div]`. Use `set g : ℕ → Formalism.REAL.UJ ε := fun k => (h1 k * h2 k) ^ k with hg`. Establish `hgK : ∀ k, g k ∈ K` using `fun k => K.pow_mem (K.mul_mem (hh1 k) (hh2 k)) k`.

Establish `hu : ∀ k : ℕ, (NormedSpace.exp ((k : ℝ)⁻¹ • ((t : ℂ) • X)) * NormedSpace.exp ((k : ℝ)⁻¹ • ((t : ℂ) • Y))) ^ k = uMat (g k)`. Introduce `k`. Rewrite using `[hg, uMat_powA, ← hs, ← hs, ← e1, ← e2]`. Both sides reduce to the same expression. Establish `hT` using `(trotter_mat ((t : ℂ) • X) ((t : ℂ) • Y)).congr hu`.

Establish `hemb` using `(Formalism.REAL.isClosedEmbeddingMatrix n ε).1`. Establish `hmem : NormedSpace.exp ((t : ℂ) • X + (t : ℂ) • Y) ∈ Set.range (fun g : Formalism.REAL.UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))` using `hemb.isClosed_range.mem_of_tendsto hT (Eventually.of_forall fun k => ⟨g k, rfl⟩)`. Take `⟨g0, hg0⟩` from `hmem`. Establish `hlim : Tendsto g atTop (𝓝 g0)`. Rewrite using `[hemb.toIsEmbedding.toIsInducing.tendsto_nhds_iff]`.

Establish `hg0' : uMat g0 = NormedSpace.exp ((t : ℂ) • X + (t : ℂ) • Y)` using `hg0`. Use `show Tendsto (fun k => uMat (g k)) atTop (𝓝 (uMat g0))`. Rewrite using `[hg0']`. Conclude with `hT`. Use `⟨g0, hK.mem_of_tendsto hlim (Eventually.of_forall hgK), ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_add]`. Conclude with `hg0`.
-/
theorem lie_add_alt : LieAdd := by
  intro n ε K hK X hX Y hY t
  have hX' : ∀ s : ℝ, ∃ h ∈ K, uMat h = NormedSpace.exp ((s : ℂ) • X) := hX
  have hY' : ∀ s : ℝ, ∃ h ∈ K, uMat h = NormedSpace.exp ((s : ℂ) • Y) := hY
  choose h1 hh1 e1 using fun k : ℕ => hX' (t / k)
  choose h2 hh2 e2 using fun k : ℕ => hY' (t / k)
  have hs : ∀ (k : ℕ) (Z : Matrix (Fin n) (Fin n) ℂ), ((t / k : ℝ) : ℂ) • Z = (k : ℝ)⁻¹ • ((t : ℂ) • Z) := by
    intro k Z
    rw [← smul_assoc, Complex.real_smul, ← Complex.ofReal_mul, inv_mul_eq_div]
  set g : ℕ → Formalism.REAL.UJ ε := fun k => (h1 k * h2 k) ^ k with hg
  have hgK : ∀ k, g k ∈ K := fun k => K.pow_mem (K.mul_mem (hh1 k) (hh2 k)) k
  have hu : ∀ k : ℕ, (NormedSpace.exp ((k : ℝ)⁻¹ • ((t : ℂ) • X)) *
      NormedSpace.exp ((k : ℝ)⁻¹ • ((t : ℂ) • Y))) ^ k = uMat (g k) := by
    intro k
    rw [hg, uMat_powA, ← hs, ← hs, ← e1, ← e2]
    rfl
  have hT := (trotter_mat ((t : ℂ) • X) ((t : ℂ) • Y)).congr hu
  have hemb := (Formalism.REAL.isClosedEmbeddingMatrix n ε).1
  have hmem : NormedSpace.exp ((t : ℂ) • X + (t : ℂ) • Y) ∈
      Set.range (fun g : Formalism.REAL.UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) :=
    hemb.isClosed_range.mem_of_tendsto hT (Eventually.of_forall fun k => ⟨g k, rfl⟩)
  obtain ⟨g0, hg0⟩ := hmem
  have hlim : Tendsto g atTop (𝓝 g0) := by
    rw [hemb.toIsEmbedding.toIsInducing.tendsto_nhds_iff]
    have hg0' : uMat g0 = NormedSpace.exp ((t : ℂ) • X + (t : ℂ) • Y) := hg0
    show Tendsto (fun k => uMat (g k)) atTop (𝓝 (uMat g0))
    rw [hg0']
    exact hT
  refine ⟨g0, hK.mem_of_tendsto hlim (Eventually.of_forall hgK), ?_⟩
  rw [smul_add]
  exact hg0

end PI.IwaMeasEx.Gauge.ZetaZeros

end

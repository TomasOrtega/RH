import Mathlib

open Filter Asymptotics NumberField

/- English proof (translation)
Establish `hlim` using `(Ideal.tendsto_norm_le_div_atTop K).comp tendsto_natCast_atTop_atTop`. Establish `hO : (fun n : ℕ ↦ (Nat.card {I : Ideal (𝓞 K) // (Ideal.absNorm I : ℝ) ≤ (n : ℝ)} : ℝ)) =O[atTop] fun n : ℕ ↦ (n : ℝ)`. Use `isBigO_of_div_tendsto_nhds ?_ _ hlim` and prove the remaining obligations. Use `filter_upwards [eventually_ne_atTop 0] with n hn h`. Conclude with `absurd (Nat.cast_eq_zero.mp h) hn`.

Simplify using `only [Real.rpow_one]`. Use `IsBigO.trans (isBigO_of_le _ fun n ↦ ?_) hO` and prove the remaining obligations. Rewrite using `[Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Nat.cast_sum, ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]`.

Simplify using `[Set.coe_eq_subtype]`.
-/
private theorem UpperTheory.Reformulated.B.Qp7.partial_sums_isBigO (K : Type*) [Field K] [NumberField K] :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n,
        (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
  have hlim := (Ideal.tendsto_norm_le_div_atTop K).comp tendsto_natCast_atTop_atTop
  have hO : (fun n : ℕ ↦ (Nat.card {I : Ideal (𝓞 K) // (Ideal.absNorm I : ℝ) ≤ (n : ℝ)} : ℝ))
      =O[atTop] fun n : ℕ ↦ (n : ℝ) := by
    refine isBigO_of_div_tendsto_nhds ?_ _ hlim
    filter_upwards [eventually_ne_atTop 0] with n hn h
    exact absurd (Nat.cast_eq_zero.mp h) hn
  simp only [Real.rpow_one]
  refine IsBigO.trans (isBigO_of_le _ fun n ↦ ?_) hO
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  calc ∑ k ∈ Finset.Icc 1 n, (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)
      ≤ ∑ k ∈ Finset.Icc 0 n, (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left zero_le_one)
          fun _ _ _ ↦ by positivity
    _ = _ := by
        rw [← Nat.cast_sum, ← Finset.card_preimage_eq_sum_card_image_eq
          (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
        simp [Set.coe_eq_subtype]

/- English proof (translation)
Establish `h` using `LSeriesSummable_of_sum_norm_bigO_and_nonneg (s := (σ : ℂ)) (UpperTheory.Reformulated.B.Qp7.partial_sums_isBigO K) (fun _ ↦ Nat.cast_nonneg _) zero_le_one (by simpa using hσ)`. Use `h.norm.congr fun n ↦ ?_` and prove the remaining obligations. Rewrite using `[LSeries.norm_term_eq]`. Use `split_ifs with hn`. Substitute `hn` using the available equality.

Simplify using `[Real.zero_rpow (zero_lt_one.trans hσ).ne']`. Simplify using `[div_eq_mul_inv]`.
-/
private theorem UpperTheory.Reformulated.B.Qp7.summable_count_mul (K : Type*) [Field K] [NumberField K] {σ : ℝ}
    (hσ : 1 < σ) :
    Summable fun n : ℕ ↦
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * ((n : ℝ) ^ σ)⁻¹ := by
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg (s := (σ : ℂ))
    (UpperTheory.Reformulated.B.Qp7.partial_sums_isBigO K) (fun _ ↦ Nat.cast_nonneg _) zero_le_one
    (by simpa using hσ)
  refine h.norm.congr fun n ↦ ?_
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · subst hn
    simp [Real.zero_rpow (zero_lt_one.trans hσ).ne']
  · simp [div_eq_mul_inv]

/- English proof (translation)
Introduce `K _ _ σ hσ`. Establish `hfin : ∀ n : ℕ, Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n}` using `fun n ↦ (Ideal.finite_setOfPred_absNorm_eq n).to_subtype`. Rewrite using `[← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) ↦ Ideal.absNorm I)).summable_iff, summable_sigma_of_nonneg (fun _ ↦ by simp only [Function.comp_apply]; positivity)]`. Use `⟨fun n ↦ Summable.of_finite, ?_⟩` and prove the remaining obligations. Use `(UpperTheory.Reformulated.B.Qp7.summable_count_mul K hσ).congr fun n ↦ ?_` and prove the remaining obligations.

Establish `: ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}, ((Ideal.absNorm I.1 : ℝ) ^ σ)⁻¹ = ((n : ℝ) ^ σ)⁻¹` using `fun I ↦ by rw [I.2]`. Simplify using `only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply, this, tsum_const, nsmul_eq_mul]`.
-/
theorem UpperTheory.Reformulated.B.Qp7.summable_absNorm_rpow_inv.{u_1} :
    ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K] {σ : ℝ},
    (1 : ℝ) < σ →
      Summable fun (I : Ideal (NumberField.RingOfIntegers K)) ↦
        ((↑((Ideal.absNorm : Ideal (NumberField.RingOfIntegers K) → ℕ) I) : ℝ) ^ σ)⁻¹ := by
  intro K _ _ σ hσ
  have hfin : ∀ n : ℕ, Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
    fun n ↦ (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  rw [← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) ↦ Ideal.absNorm I)).summable_iff,
    summable_sigma_of_nonneg (fun _ ↦ by simp only [Function.comp_apply]; positivity)]
  refine ⟨fun n ↦ Summable.of_finite, ?_⟩
  refine (UpperTheory.Reformulated.B.Qp7.summable_count_mul K hσ).congr fun n ↦ ?_
  have : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
      ((Ideal.absNorm I.1 : ℝ) ^ σ)⁻¹ = ((n : ℝ) ^ σ)⁻¹ := fun I ↦ by rw [I.2]
  simp only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply, this, tsum_const, nsmul_eq_mul]

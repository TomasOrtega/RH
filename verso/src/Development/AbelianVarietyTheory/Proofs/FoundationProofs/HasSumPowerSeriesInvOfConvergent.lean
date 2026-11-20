import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau

namespace GlobalTheory

namespace PowerSeriesInv

/- English proof (translation)
Establish `hc0 : PowerSeries.constantCoeff (PowerSeries.mk a) = a 0`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]`. Use `set A := ‖a 0‖ with hA`. Establish `hA0 : 0 < A` using `norm_pos_iff.mpr ha0`. Establish `hMA : A ≤ M` using `by simpa using hM 0`.

Establish `hM0 : 0 < M` using `lt_of_lt_of_le hA0 hMA`. Use `set m := M / A with hm`. Establish `hm0 : 0 < m` using `div_pos hM0 hA0`. Use `set K := R * (1 + m) with hK`. Use `set q := (1 + m)⁻¹ with hq`.

Establish `hK0 : 0 < K` using `by positivity`. Establish `hq0 : 0 ≤ q` using `by positivity`. Establish `hq1 : q < 1` using `inv_lt_one_of_one_lt₀ (by linarith)`. Establish `hRK : R = K * q`. Rewrite using `[hK, hq, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]`.

Establish `hqA : q / (1 - q) = A / M`. Establish `hqpos : 0 < q` using `by positivity`. Establish `h1q : 1 - q = m * q`. Establish `: (1 + m) * q = 1` using `mul_inv_cancel₀ (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[h1q, hm]`. Clear the denominators using the available nonvanishing facts. Establish `hgeom : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), (if 1 ≤ k then q ^ k else 0) ≤ A / M`. Introduce `n`. Rewrite using `[Finset.sum_range_succ']`.

Simplify using `only [show ∀ k : ℕ, 1 ≤ k + 1 from fun k => by omega, if_true, show ¬ (1 ≤ 0) from by omega, if_false, add_zero]`. Repeatedly rewrite using `[pow_succ]`. Rewrite using `[← Finset.sum_mul]`. Establish `h` using `geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hq0 hq1`. Rewrite `h` using `[← Finset.range_eq_Ico, pow_zero]`.

Combine the equalities or inequalities in the displayed calculation. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Rewrite using `[PowerSeries.coeff_inv]`. Use `split_ifs with hn`.

Substitute `hn` using the available equality. Simplify using `[hc0, hA]`. Establish `hterm : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n, ‖(if p.2 < n then PowerSeries.coeff p.1 (PowerSeries.mk a) * PowerSeries.coeff p.2 (PowerSeries.mk a)⁻¹ else 0)‖ ≤ M * A⁻¹ * K ^ n * (if 1 ≤ p.1 then q ^ p.1 else 0)`. Introduce `p hp`. Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`.

Use `split_ifs with h1 h2 h2`. Rewrite using `[norm_mul, PowerSeries.coeff_mk]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hRK, ← hp, mul_pow, pow_add]`. Expand and normalize the polynomial expressions, which then agree.

Use linear arithmetic over natural numbers and integers. Simplify using `only [norm_zero]`. Check the signs of the components of the expression. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[norm_mul, norm_neg, norm_inv, hc0]`. Use `_ ≤ A⁻¹ * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, M * A⁻¹ * K ^ n * (if 1 ≤ p.1 then q ^ p.1 else 0) := mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm)) (by positivity)`. Use `_ = A⁻¹ * (M * A⁻¹ * K ^ n * ∑ k ∈ Finset.range (n + 1), (if 1 ≤ k then q ^ k else 0)) := by`. Rewrite using `[← Finset.mul_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]`. Use `_ ≤ A⁻¹ * (M * A⁻¹ * K ^ n * (A / M)) := by gcongr`.

Conclude with `hgeom n`. Use `_ = A⁻¹ * K ^ n := by`. Clear the denominators using the available nonvanishing facts.
-/
theorem coeff_inv_norm_le (a : ℕ → ℂ) (M R : ℝ) (hR : 0 < R) (ha0 : a 0 ≠ 0)
    (hM : ∀ n, ‖a n‖ ≤ M * R ^ n) (n : ℕ) :
    ‖PowerSeries.coeff n (PowerSeries.mk a)⁻¹‖ ≤ ‖a 0‖⁻¹ * (R * (1 + M / ‖a 0‖)) ^ n := by
  have hc0 : PowerSeries.constantCoeff (PowerSeries.mk a) = a 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  set A := ‖a 0‖ with hA
  have hA0 : 0 < A := norm_pos_iff.mpr ha0
  have hMA : A ≤ M := by simpa using hM 0
  have hM0 : 0 < M := lt_of_lt_of_le hA0 hMA
  set m := M / A with hm
  have hm0 : 0 < m := div_pos hM0 hA0
  set K := R * (1 + m) with hK
  set q := (1 + m)⁻¹ with hq
  have hK0 : 0 < K := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hRK : R = K * q := by
    rw [hK, hq, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
  have hqA : q / (1 - q) = A / M := by
    have hqpos : 0 < q := by positivity
    have h1q : 1 - q = m * q := by
      have : (1 + m) * q = 1 := mul_inv_cancel₀ (by positivity)
      linarith
    rw [h1q, hm]
    field_simp
  have hgeom : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), (if 1 ≤ k then q ^ k else 0) ≤ A / M := by
    intro n
    rw [Finset.sum_range_succ']
    simp only [show ∀ k : ℕ, 1 ≤ k + 1 from fun k => by omega, if_true,
      show ¬ (1 ≤ 0) from by omega, if_false, add_zero]
    simp_rw [pow_succ]
    rw [← Finset.sum_mul]
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hq0 hq1
    rw [← Finset.range_eq_Ico, pow_zero] at h
    calc (∑ i ∈ Finset.range n, q ^ i) * q ≤ 1 / (1 - q) * q := by gcongr
      _ = q / (1 - q) := by ring
      _ = A / M := hqA
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [PowerSeries.coeff_inv]
  split_ifs with hn
  · subst hn
    simp [hc0, hA]
  · have hterm : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        ‖(if p.2 < n then PowerSeries.coeff p.1 (PowerSeries.mk a) *
            PowerSeries.coeff p.2 (PowerSeries.mk a)⁻¹ else 0)‖ ≤
          M * A⁻¹ * K ^ n * (if 1 ≤ p.1 then q ^ p.1 else 0) := by
      intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      split_ifs with h1 h2 h2
      · rw [norm_mul, PowerSeries.coeff_mk]
        calc ‖a p.1‖ * ‖PowerSeries.coeff p.2 (PowerSeries.mk a)⁻¹‖
            ≤ (M * R ^ p.1) * (A⁻¹ * K ^ p.2) :=
              mul_le_mul (hM _) (ih _ h1) (norm_nonneg _) (by positivity)
          _ = M * A⁻¹ * K ^ n * q ^ p.1 := by
              rw [hRK, ← hp, mul_pow, pow_add]; ring
      · omega
      · simp only [norm_zero]; positivity
      · simp
    calc ‖-(PowerSeries.constantCoeff (PowerSeries.mk a))⁻¹ *
          ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (if p.2 < n then PowerSeries.coeff p.1 (PowerSeries.mk a) *
            PowerSeries.coeff p.2 (PowerSeries.mk a)⁻¹ else 0)‖
        = A⁻¹ * ‖∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (if p.2 < n then
            PowerSeries.coeff p.1 (PowerSeries.mk a) *
            PowerSeries.coeff p.2 (PowerSeries.mk a)⁻¹ else 0)‖ := by
          rw [norm_mul, norm_neg, norm_inv, hc0]
      _ ≤ A⁻¹ * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, M * A⁻¹ * K ^ n * (if 1 ≤ p.1 then q ^ p.1 else 0) :=
          mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm))
            (by positivity)
      _ = A⁻¹ * (M * A⁻¹ * K ^ n *
            ∑ k ∈ Finset.range (n + 1), (if 1 ≤ k then q ^ k else 0)) := by
          rw [← Finset.mul_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      _ ≤ A⁻¹ * (M * A⁻¹ * K ^ n * (A / M)) := by
          gcongr
          exact hgeom n
      _ = A⁻¹ * K ^ n := by
          field_simp

/- English proof (translation)
Introduce `a ρ hρ ha0 hs`. Use `set x0 : ℂ := ((ρ / 2 : ℝ) : ℂ) with hx0def`. Establish `hx0 : ‖x0‖ = ρ / 2`. Rewrite using `[hx0def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]`. Establish `hsum` using `hs x0 (by rw [hx0]; linarith)`.

Establish `htend` using `hsum.tendsto_atTop_zero.norm`. Take `⟨M, hM⟩` from `htend.bddAbove_range`. Use `set R : ℝ := 2 / ρ with hRdef`. Establish `hR : 0 < R` using `by positivity`. Establish `hMa : ∀ n, ‖a n‖ ≤ M * R ^ n`.

Introduce `n`. Establish `h1 : ‖a n * x0 ^ n‖ ≤ M` using `hM ⟨n, rfl⟩`. Rewrite `h1` using `[norm_mul, norm_pow, hx0]`. Establish `h2 : (ρ / 2) ^ n * R ^ n = 1`. Rewrite using `[← mul_pow, hRdef, div_mul_div_comm, mul_comm ρ 2, div_self (by positivity), one_pow]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hA0 : 0 < ‖a 0‖` using `norm_pos_iff.mpr ha0`. Establish `hM0 : 0 < M` using `lt_of_lt_of_le hA0 (by simpa using hMa 0)`. Use `set K := R * (1 + M / ‖a 0‖) with hKdef`. Establish `hK : 0 < K` using `by positivity`.

Use `⟨min (ρ / 2) K⁻¹, by positivity, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Establish `hx1 : ‖x‖ < ρ / 2` using `lt_of_lt_of_le hx (min_le_left _ _)`. Establish `hx2 : ‖x‖ < K⁻¹` using `lt_of_lt_of_le hx (min_le_right _ _)`. Establish `hRx : R * ‖x‖ < 1`.

Rewrite using `[hRdef, div_mul_eq_mul_div, div_lt_one hρ]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hKx : K * ‖x‖ < 1`. Use `mul_lt_mul_of_pos_left hx2 hK` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel₀ hK.ne']`. Then use the resulting hypothesis.

Establish `hsa : Summable fun n => ‖a n * x ^ n‖`. Use `Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) ((summable_geometric_of_lt_one (by positivity) hRx).mul_left M)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow]`. Combine the equalities or inequalities in the displayed calculation. Establish `hsb : Summable fun n => ‖PowerSeries.coeff n (PowerSeries.mk a)⁻¹ * x ^ n‖`.

Use `Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) ((summable_geometric_of_lt_one (by positivity) hKx).mul_left ‖a 0‖⁻¹)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow]`. Combine the equalities or inequalities in the displayed calculation. Establish `hc0 : PowerSeries.constantCoeff (PowerSeries.mk a) ≠ 0`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]`.

Conclude with `ha0`. Establish `hc : ∀ n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, a kl.1 * x ^ kl.1 * (PowerSeries.coeff kl.2 (PowerSeries.mk a)⁻¹ * x ^ kl.2) = (if n = 0 then 1 else 0)`. Introduce `n`. Establish `h` using `congrArg (PowerSeries.coeff n) (PowerSeries.mul_inv_cancel (PowerSeries.mk a) hc0)`. Rewrite `h` using `[PowerSeries.coeff_mul, PowerSeries.coeff_one]`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl (fun kl hkl => ?_)` and prove the remaining obligations. Rewrite `hkl` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Rewrite using `[← hkl, pow_add, PowerSeries.coeff_mk]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = (if n = 0 then 1 else 0) := by`. Apply the tactic sequence `rw [← Finset.sum_mul, h]; split_ifs with hn <;> simp [hn]`. Establish `key : (∑' n, a n * x ^ n) * (∑' n, PowerSeries.coeff n (PowerSeries.mk a)⁻¹ * x ^ n) = 1`. Rewrite using `[tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsa hsb, tsum_congr hc]`. Conclude with `tsum_ite_eq 0 1`.

Use `⟨left_ne_zero_of_mul_eq_one key, ?_⟩` and prove the remaining obligations. Rewrite using `[← eq_inv_of_mul_eq_one_right key]`. Conclude with `(Summable.of_norm hsb).hasSum`.
-/
theorem hasSum_inv :
    ∀ (a : ℕ → ℂ) (ρ : ℝ), 0 < ρ → a 0 ≠ 0 → (∀ x : ℂ, ‖x‖ < ρ → Summable fun n => a n * x ^ n) →
      ∃ ρ' : ℝ, 0 < ρ' ∧ ∀ x : ℂ, ‖x‖ < ρ' → (∑' n, a n * x ^ n) ≠ 0 ∧
        HasSum (fun n => PowerSeries.coeff n (PowerSeries.mk a)⁻¹ * x ^ n)
          (∑' n, a n * x ^ n)⁻¹ := by
  intro a ρ hρ ha0 hs
  set x0 : ℂ := ((ρ / 2 : ℝ) : ℂ) with hx0def
  have hx0 : ‖x0‖ = ρ / 2 := by
    rw [hx0def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hsum := hs x0 (by rw [hx0]; linarith)
  have htend := hsum.tendsto_atTop_zero.norm
  obtain ⟨M, hM⟩ := htend.bddAbove_range
  set R : ℝ := 2 / ρ with hRdef
  have hR : 0 < R := by positivity
  have hMa : ∀ n, ‖a n‖ ≤ M * R ^ n := by
    intro n
    have h1 : ‖a n * x0 ^ n‖ ≤ M := hM ⟨n, rfl⟩
    rw [norm_mul, norm_pow, hx0] at h1
    have h2 : (ρ / 2) ^ n * R ^ n = 1 := by
      rw [← mul_pow, hRdef, div_mul_div_comm, mul_comm ρ 2, div_self (by positivity), one_pow]
    calc ‖a n‖ = ‖a n‖ * (ρ / 2) ^ n * R ^ n := by rw [mul_assoc, h2, mul_one]
      _ ≤ M * R ^ n := by gcongr
  have hA0 : 0 < ‖a 0‖ := norm_pos_iff.mpr ha0
  have hM0 : 0 < M := lt_of_lt_of_le hA0 (by simpa using hMa 0)
  set K := R * (1 + M / ‖a 0‖) with hKdef
  have hK : 0 < K := by positivity
  refine ⟨min (ρ / 2) K⁻¹, by positivity, ?_⟩
  intro x hx
  have hx1 : ‖x‖ < ρ / 2 := lt_of_lt_of_le hx (min_le_left _ _)
  have hx2 : ‖x‖ < K⁻¹ := lt_of_lt_of_le hx (min_le_right _ _)
  have hRx : R * ‖x‖ < 1 := by
    rw [hRdef, div_mul_eq_mul_div, div_lt_one hρ]; linarith
  have hKx : K * ‖x‖ < 1 := by
    have := mul_lt_mul_of_pos_left hx2 hK
    rwa [mul_inv_cancel₀ hK.ne'] at this
  have hsa : Summable fun n => ‖a n * x ^ n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one (by positivity) hRx).mul_left M)
    rw [norm_mul, norm_pow]
    calc ‖a n‖ * ‖x‖ ^ n ≤ M * R ^ n * ‖x‖ ^ n := by gcongr; exact hMa n
      _ = M * (R * ‖x‖) ^ n := by ring
  have hsb : Summable fun n => ‖PowerSeries.coeff n (PowerSeries.mk a)⁻¹ * x ^ n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one (by positivity) hKx).mul_left ‖a 0‖⁻¹)
    rw [norm_mul, norm_pow]
    calc ‖PowerSeries.coeff n (PowerSeries.mk a)⁻¹‖ * ‖x‖ ^ n
        ≤ ‖a 0‖⁻¹ * K ^ n * ‖x‖ ^ n := by
          gcongr; exact coeff_inv_norm_le a M R hR ha0 hMa n
      _ = ‖a 0‖⁻¹ * (K * ‖x‖) ^ n := by ring_nf
  have hc0 : PowerSeries.constantCoeff (PowerSeries.mk a) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]; exact ha0
  have hc : ∀ n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      a kl.1 * x ^ kl.1 * (PowerSeries.coeff kl.2 (PowerSeries.mk a)⁻¹ * x ^ kl.2) =
        (if n = 0 then 1 else 0) := by
    intro n
    have h := congrArg (PowerSeries.coeff n) (PowerSeries.mul_inv_cancel (PowerSeries.mk a) hc0)
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_one] at h
    calc ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
          a kl.1 * x ^ kl.1 * (PowerSeries.coeff kl.2 (PowerSeries.mk a)⁻¹ * x ^ kl.2)
        = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, (PowerSeries.coeff kl.1 (PowerSeries.mk a) *
            PowerSeries.coeff kl.2 (PowerSeries.mk a)⁻¹) * x ^ n := by
          refine Finset.sum_congr rfl (fun kl hkl => ?_)
          rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
          rw [← hkl, pow_add, PowerSeries.coeff_mk]; ring
      _ = (if n = 0 then 1 else 0) := by
          rw [← Finset.sum_mul, h]; split_ifs with hn <;> simp [hn]
  have key : (∑' n, a n * x ^ n) * (∑' n, PowerSeries.coeff n (PowerSeries.mk a)⁻¹ * x ^ n) = 1 := by
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsa hsb, tsum_congr hc]
    exact tsum_ite_eq 0 1
  refine ⟨left_ne_zero_of_mul_eq_one key, ?_⟩
  rw [← eq_inv_of_mul_eq_one_right key]
  exact (Summable.of_norm hsb).hasSum

end PowerSeriesInv

end GlobalTheory

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumPrimeLogDivPredLeLogAdd

open Finset

namespace LevelTowerAlt

/- English proof (translation)
Establish `hB2 : (2 : ℝ) ≤ B` using `by exact_mod_cast hB`. Establish `hBp : (B : ℝ) + 1 ≤ p` using `by exact_mod_cast h`. Establish `hB0 : (0 : ℝ) < B` using `by linarith`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Establish `hp1 : (0 : ℝ) < (p : ℝ) - 1` using `by linarith`.

Establish `hlogB : 0.6931471803 < Real.log B` using `Real.log_two_gt_d9.trans_le (Real.log_le_log (by norm_num) hB2)`. Establish `hratio : Real.log ((p : ℝ) / B) ≤ (p : ℝ) / B - 1` using `Real.log_le_sub_one_of_pos (div_pos hp0 hB0)`. Rewrite `hratio` using `[Real.log_div hp0.ne' hB0.ne']`. Establish `key : Real.log p * B ≤ B * Real.log B + ((p : ℝ) - B)`. Establish `h1` using `mul_le_mul_of_nonneg_right hratio hB0.le`.

Rewrite `h1` using `[sub_mul, sub_mul, div_mul_cancel₀ _ hB0.ne', one_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[div_le_div_iff₀ hp1 hB0]`. Establish `h3 : 0 ≤ 3 * ((p : ℝ) - 1) - B` using `by linarith`. Establish `h4` using `mul_le_mul_of_nonneg_right hlogB.le h3`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem log_div_pred_le (p B : ℕ) (hB : 2 ≤ B) (h : B < p) :
    Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ 3 * Real.log B / B := by
  have hB2 : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hBp : (B : ℝ) + 1 ≤ p := by exact_mod_cast h
  have hB0 : (0 : ℝ) < B := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hlogB : 0.6931471803 < Real.log B :=
    Real.log_two_gt_d9.trans_le (Real.log_le_log (by norm_num) hB2)
  have hratio : Real.log ((p : ℝ) / B) ≤ (p : ℝ) / B - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hp0 hB0)
  rw [Real.log_div hp0.ne' hB0.ne'] at hratio
  have key : Real.log p * B ≤ B * Real.log B + ((p : ℝ) - B) := by
    have h1 := mul_le_mul_of_nonneg_right hratio hB0.le
    rw [sub_mul, sub_mul, div_mul_cancel₀ _ hB0.ne', one_mul] at h1
    linarith
  rw [div_le_div_iff₀ hp1 hB0]
  have h3 : 0 ≤ 3 * ((p : ℝ) - 1) - B := by linarith
  have h4 := mul_le_mul_of_nonneg_right hlogB.le h3
  nlinarith

/- English proof (translation)
Use `⟨8, by norm_num, fun S S₀ B hB hS hcard => ?_⟩` and prove the remaining obligations. Establish `hB2 : (2 : ℝ) ≤ B` using `by exact_mod_cast hB`. Establish `hB0 : (0 : ℝ) < B` using `by linarith`. Establish `hBne : (B : ℝ) ≠ 0` using `hB0.ne'`. Establish `hlogB : 0.6931471803 < Real.log B` using `Real.log_two_gt_d9.trans_le (Real.log_le_log (by norm_num) hB2)`.

Rewrite using `[← Finset.sum_filter_add_sum_filter_not S (fun p => p ≤ B)]`. Establish `hsmall : ∑ p ∈ S with p ≤ B, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ Real.log B + 2.2`. Use `le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (GlobalTheory.PrimeLogSum.sum_log_div_pred_le B)` and prove the remaining obligations. Introduce `p hp`. Rewrite `hp`, the goal using `[Finset.mem_filter]`.

Conclude with `⟨Finset.mem_range.2 (Nat.lt_succ_of_le hp.2), (hS p hp.1).1⟩`. Introduce `p hp _`. Establish `hpr` using `(Finset.mem_filter.1 hp).2`. Establish `h2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hpr.two_le`. Conclude with `div_nonneg (Real.log_nonneg (by linarith)) (by linarith)`.

Establish `hlarge : ∑ p ∈ S with ¬ p ≤ B, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ 3 * Real.log B`. Establish `hsub : S.filter (fun p => ¬ p ≤ B) ⊆ S₀`. Introduce `p hp`. Rewrite `hp` using `[Finset.mem_filter]`. Conclude with `(hS p hp.1).2.resolve_left hp.2`.

Establish `hc : ((S.filter (fun p => ¬ p ≤ B)).card : ℝ) ≤ B`. Conclude with `(Finset.card_le_card hsub).trans hcard` after adjusting the coercions. Use `(Finset.sum_le_card_nsmul _ _ (3 * Real.log B / B) ?_).trans ?_` and prove the remaining obligations. Introduce `p hp`. Rewrite `hp` using `[Finset.mem_filter]`.

Conclude with `LevelTowerAlt.log_div_pred_le p B hB (not_le.1 hp.2)`. Rewrite using `[nsmul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_log_prime_ratio_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (S S₀ : Finset ℕ) (B : ℕ), 2 ≤ B → (∀ p ∈ S, p.Prime ∧ (p ≤ B ∨ p ∈ S₀)) → S₀.card ≤ B → ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ C * Real.log B := by
  refine ⟨8, by norm_num, fun S S₀ B hB hS hcard => ?_⟩
  have hB2 : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := by linarith
  have hBne : (B : ℝ) ≠ 0 := hB0.ne'
  have hlogB : 0.6931471803 < Real.log B :=
    Real.log_two_gt_d9.trans_le (Real.log_le_log (by norm_num) hB2)
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p => p ≤ B)]
  have hsmall : ∑ p ∈ S with p ≤ B, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ Real.log B + 2.2 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
      (GlobalTheory.PrimeLogSum.sum_log_div_pred_le B)
    · intro p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hp.2), (hS p hp.1).1⟩
    · intro p hp _
      have hpr := (Finset.mem_filter.1 hp).2
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hpr.two_le
      exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  have hlarge : ∑ p ∈ S with ¬ p ≤ B, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ 3 * Real.log B := by
    have hsub : S.filter (fun p => ¬ p ≤ B) ⊆ S₀ := by
      intro p hp
      rw [Finset.mem_filter] at hp
      exact (hS p hp.1).2.resolve_left hp.2
    have hc : ((S.filter (fun p => ¬ p ≤ B)).card : ℝ) ≤ B := by
      exact_mod_cast (Finset.card_le_card hsub).trans hcard
    refine (Finset.sum_le_card_nsmul _ _ (3 * Real.log B / B) ?_).trans ?_
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact LevelTowerAlt.log_div_pred_le p B hB (not_le.1 hp.2)
    · rw [nsmul_eq_mul]
      calc _ ≤ (B : ℝ) * (3 * Real.log B / B) :=
            mul_le_mul_of_nonneg_right hc (div_nonneg (by linarith) hB0.le)
        _ = 3 * Real.log B := by field_simp
  linarith

end LevelTowerAlt

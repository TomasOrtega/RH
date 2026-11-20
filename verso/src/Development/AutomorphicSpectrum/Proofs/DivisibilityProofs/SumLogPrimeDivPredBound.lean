import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumLogDivPredLe

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Establish `hB0 : (0 : ℝ) < B`. Establish `: (128 : ℝ) ≤ B` using `by exact_mod_cast hB`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpB : (B : ℝ) + 1 ≤ p` using `by exact_mod_cast hp`. Establish `hp1 : (0 : ℝ) < (p : ℝ) - 1` using `by linarith`.

Establish `hB1 : (0 : ℝ) < (B : ℝ) + 1` using `by linarith`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Establish `hlog : Real.log p ≤ Real.log ((B : ℝ) + 1) + ((p : ℝ) - B - 1) / ((B : ℝ) + 1)`. Establish `h1` using `Real.log_le_sub_one_of_pos (div_pos hp0 hB1)`. Rewrite `h1` using `[Real.log_div hp0.ne' hB1.ne']`.

Establish `h2 : (p : ℝ) / ((B : ℝ) + 1) - 1 = ((p : ℝ) - B - 1) / ((B : ℝ) + 1)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[div_le_div_iff₀ hp1 hB0]`.

Establish `hd : (0 : ℝ) ≤ (p : ℝ) - B - 1` using `by linarith`. Establish `hfrac : (B : ℝ) * (((p : ℝ) - B - 1) / ((B : ℝ) + 1)) ≤ ((p : ℝ) - B - 1) * Real.log ((B : ℝ) + 1)`. Establish `h3 : (B : ℝ) / ((B : ℝ) + 1) ≤ Real.log ((B : ℝ) + 1)`. Use `le_trans ?_ hL` and prove the remaining obligations. Rewrite using `[div_le_one hB1]`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Establish `h4 : Real.log p * B ≤ (Real.log ((B : ℝ) + 1) + ((p : ℝ) - B - 1) / ((B : ℝ) + 1)) * B` using `mul_le_mul_of_nonneg_right hlog hB0.le`. Use polynomial arithmetic with `[h4, hfrac]`.
-/
theorem log_div_pred_le_of_lt (B p : ℕ) (hB : 128 ≤ B) (hp : B < p) (hL : 1 ≤ Real.log ((B : ℝ) + 1)) :
    Real.log p / ((p : ℝ) - 1) ≤ Real.log ((B : ℝ) + 1) / B := by
  have hB0 : (0 : ℝ) < B := by
    have : (128 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have hpB : (B : ℝ) + 1 ≤ p := by exact_mod_cast hp
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hB1 : (0 : ℝ) < (B : ℝ) + 1 := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hlog : Real.log p ≤ Real.log ((B : ℝ) + 1) + ((p : ℝ) - B - 1) / ((B : ℝ) + 1) := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hp0 hB1)
    rw [Real.log_div hp0.ne' hB1.ne'] at h1
    have h2 : (p : ℝ) / ((B : ℝ) + 1) - 1 = ((p : ℝ) - B - 1) / ((B : ℝ) + 1) := by
      field_simp
      ring
    linarith
  rw [div_le_div_iff₀ hp1 hB0]
  have hd : (0 : ℝ) ≤ (p : ℝ) - B - 1 := by linarith
  have hfrac : (B : ℝ) * (((p : ℝ) - B - 1) / ((B : ℝ) + 1)) ≤ ((p : ℝ) - B - 1) * Real.log ((B : ℝ) + 1) := by
    have h3 : (B : ℝ) / ((B : ℝ) + 1) ≤ Real.log ((B : ℝ) + 1) := by
      refine le_trans ?_ hL
      rw [div_le_one hB1]
      linarith
    calc (B : ℝ) * (((p : ℝ) - B - 1) / ((B : ℝ) + 1))
        = ((p : ℝ) - B - 1) * ((B : ℝ) / ((B : ℝ) + 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 hd
  have h4 : Real.log p * B ≤ (Real.log ((B : ℝ) + 1) + ((p : ℝ) - B - 1) / ((B : ℝ) + 1)) * B :=
    mul_le_mul_of_nonneg_right hlog hB0.le
  nlinarith [h4, hfrac]

/- English proof (translation)
Introduce `B bad S hB hcard hS`. Establish `hBR : (128 : ℝ) ≤ B` using `by exact_mod_cast hB`. Establish `hB0 : (0 : ℝ) < B` using `by linarith`. Establish `hlogB : (4.85 : ℝ) ≤ Real.log B`. Establish `h128 : Real.log 128 = 7 * Real.log 2`.

Rewrite using `[show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]`. Evaluate the numerical expressions. Establish `h2` using `Real.log_two_gt_d9`. Establish `h3 : Real.log 128 ≤ Real.log B` using `Real.log_le_log (by norm_num) hBR`. Rewrite `h3` using `[h128]`.

Evaluate the numerical expressions using `at h2 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hLle : Real.log ((B : ℝ) + 1) ≤ Real.log B + 1 / B`. Establish `hpos : (0 : ℝ) < ((B : ℝ) + 1) / B` using `by positivity`. Establish `h1` using `Real.log_le_sub_one_of_pos hpos`.

Rewrite `h1` using `[Real.log_div (by positivity) hB0.ne']`. Establish `h2 : ((B : ℝ) + 1) / B - 1 = 1 / B`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hLge : 1 ≤ Real.log ((B : ℝ) + 1)`. Establish `: Real.log B ≤ Real.log ((B : ℝ) + 1)` using `Real.log_le_log hB0 (by linarith)`. Evaluate the numerical expressions using `at hlogB`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hinv : 1 / (B : ℝ) ≤ 1`.

Rewrite using `[div_le_one hB0]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[← Finset.sum_filter_add_sum_filter_not S (fun p => p ≤ B)]`. Establish `hsmall : ∑ p ∈ S.filter (fun p => p ≤ B), Real.log p / ((p : ℝ) - 1) ≤ Real.log B + 17 / 5`. Use `GlobalTheory.CompanionTheory.Ar.Small.sum_log_div_pred_le (B : ℝ) _ (by linarith) ?_` and prove the remaining obligations.

Introduce `p hp`. Take `⟨hpS, hpB⟩` from `Finset.mem_filter.mp hp`. Conclude with `⟨(hS p hpS).1, by exact_mod_cast hpB⟩`. Establish `hlarge : ∑ p ∈ S.filter (fun p => ¬ p ≤ B), Real.log p / ((p : ℝ) - 1) ≤ Real.log ((B : ℝ) + 1)`. Establish `hsub : S.filter (fun p => ¬ p ≤ B) ⊆ bad`.

Introduce `p hp`. Take `⟨hpS, hpB⟩` from `Finset.mem_filter.mp hp`. Conclude with `(hS p hpS).2.resolve_left hpB`. Establish `hc : (S.filter (fun p => ¬ p ≤ B)).card ≤ B` using `(Finset.card_le_card hsub).trans hcard`. Establish `h1 : ∑ p ∈ S.filter (fun p => ¬ p ≤ B), Real.log p / ((p : ℝ) - 1) ≤ (S.filter (fun p => ¬ p ≤ B)).card • (Real.log ((B : ℝ) + 1) / B)`.

Use `Finset.sum_le_card_nsmul _ _ _ ?_` and prove the remaining obligations. Introduce `p hp`. Conclude with `log_div_pred_le_of_lt B p hB (not_le.mp (Finset.mem_filter.mp hp).2) hLge`. Establish `h2 : (S.filter (fun p => ¬ p ≤ B)).card • (Real.log ((B : ℝ) + 1) / B) ≤ (B : ℝ) * (Real.log ((B : ℝ) + 1) / B)`. Rewrite using `[nsmul_eq_mul]`.

Use `mul_le_mul_of_nonneg_right (by exact_mod_cast hc) ?_` and prove the remaining obligations. Conclude with `div_nonneg (by linarith) hB0.le`. Establish `h3 : (B : ℝ) * (Real.log ((B : ℝ) + 1) / B) = Real.log ((B : ℝ) + 1)`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion.

Evaluate the numerical expressions using `at hlogB`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_log_div_pred_SB :
    ∀ (B : ℕ) (bad S : Finset ℕ), 128 ≤ B → bad.card ≤ B →
      (∀ p ∈ S, p.Prime ∧ (p ≤ B ∨ p ∈ bad)) →
      ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 3 * Real.log B + 1 := by
  intro B bad S hB hcard hS
  have hBR : (128 : ℝ) ≤ B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := by linarith
  have hlogB : (4.85 : ℝ) ≤ Real.log B := by
    have h128 : Real.log 128 = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
      norm_num
    have h2 := Real.log_two_gt_d9
    have h3 : Real.log 128 ≤ Real.log B := Real.log_le_log (by norm_num) hBR
    rw [h128] at h3
    norm_num at h2 ⊢
    linarith
  have hLle : Real.log ((B : ℝ) + 1) ≤ Real.log B + 1 / B := by
    have hpos : (0 : ℝ) < ((B : ℝ) + 1) / B := by positivity
    have h1 := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_div (by positivity) hB0.ne'] at h1
    have h2 : ((B : ℝ) + 1) / B - 1 = 1 / B := by
      field_simp
      ring
    linarith
  have hLge : 1 ≤ Real.log ((B : ℝ) + 1) := by
    have : Real.log B ≤ Real.log ((B : ℝ) + 1) := Real.log_le_log hB0 (by linarith)
    norm_num at hlogB
    linarith
  have hinv : 1 / (B : ℝ) ≤ 1 := by
    rw [div_le_one hB0]
    linarith
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p => p ≤ B)]
  have hsmall : ∑ p ∈ S.filter (fun p => p ≤ B), Real.log p / ((p : ℝ) - 1)
      ≤ Real.log B + 17 / 5 := by
    refine GlobalTheory.CompanionTheory.Ar.Small.sum_log_div_pred_le (B : ℝ) _ (by linarith) ?_
    intro p hp
    obtain ⟨hpS, hpB⟩ := Finset.mem_filter.mp hp
    exact ⟨(hS p hpS).1, by exact_mod_cast hpB⟩
  have hlarge : ∑ p ∈ S.filter (fun p => ¬ p ≤ B), Real.log p / ((p : ℝ) - 1)
      ≤ Real.log ((B : ℝ) + 1) := by
    have hsub : S.filter (fun p => ¬ p ≤ B) ⊆ bad := by
      intro p hp
      obtain ⟨hpS, hpB⟩ := Finset.mem_filter.mp hp
      exact (hS p hpS).2.resolve_left hpB
    have hc : (S.filter (fun p => ¬ p ≤ B)).card ≤ B :=
      (Finset.card_le_card hsub).trans hcard
    have h1 : ∑ p ∈ S.filter (fun p => ¬ p ≤ B), Real.log p / ((p : ℝ) - 1)
        ≤ (S.filter (fun p => ¬ p ≤ B)).card • (Real.log ((B : ℝ) + 1) / B) := by
      refine Finset.sum_le_card_nsmul _ _ _ ?_
      intro p hp
      exact log_div_pred_le_of_lt B p hB (not_le.mp (Finset.mem_filter.mp hp).2) hLge
    have h2 : (S.filter (fun p => ¬ p ≤ B)).card • (Real.log ((B : ℝ) + 1) / B)
        ≤ (B : ℝ) * (Real.log ((B : ℝ) + 1) / B) := by
      rw [nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right (by exact_mod_cast hc) ?_
      exact div_nonneg (by linarith) hB0.le
    have h3 : (B : ℝ) * (Real.log ((B : ℝ) + 1) / B) = Real.log ((B : ℝ) + 1) := by
      field_simp
    linarith
  norm_num at hlogB
  linarith

end GlobalTheory.CompanionTheory.Ar.Flat

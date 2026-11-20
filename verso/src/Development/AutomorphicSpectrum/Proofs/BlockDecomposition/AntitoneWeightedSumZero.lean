import Mathlib

namespace GlobalTheory.CompanionTheory.Tempered

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Supply the required witnesses or components.

Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem weighted_antitone_eq_zero_of_tails_nonneg :
    ∀ (h : ℕ) (d e : Fin h → ℝ), (∀ i, 0 < d i) → Antitone e → ∑ i, d i * e i = 0 →
      (∀ j : Fin h, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => j ≤ i), d i * e i) →
      ∀ i, e i = 0 := by
  intro h d e hd he hsum htail
  have hnn : ∀ i, 0 ≤ e i := by
    intro i
    by_contra hneg
    rw [not_le] at hneg
    have hlt : ∑ k ∈ Finset.univ.filter (fun k => i ≤ k), d k * e k < 0 := by
      apply Finset.sum_neg
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        exact mul_neg_of_pos_of_neg (hd k) (lt_of_le_of_lt (he hk) hneg)
      · exact ⟨i, by simp⟩
    linarith [htail i]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (hd k).le (hnn k)).1 hsum
  intro i
  rcases mul_eq_zero.1 (hz i (Finset.mem_univ i)) with h1 | h1
  · exact absurd h1 (hd i).ne'
  · exact h1

end GlobalTheory.CompanionTheory.Tempered

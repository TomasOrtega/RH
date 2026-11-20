import Mathlib

namespace GlobalTheory.ClosedSubgroupCriterion

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis.

Rewrite the indicated hypotheses using the stated equalities. Evaluate the numerical expressions. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers.

Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. It suffices to derive a contradiction. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Evaluate the numerical expressions. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem main : ∀ {n j : ℕ} (a : Fin n → ℤ), Antitone a → (∀ (i : Fin n), a i = (0 : ℤ) ∨ a i = (1 : ℤ)) →
    Finset.card {i : Fin n | a i = (1 : ℤ)} = j → ∀ (i : Fin n), a i = (1 : ℤ) ↔ (↑i : ℕ) < j := by
  intro n j a ha h01 hj i
  constructor
  · intro hi
    by_contra hlt
    push_neg at hlt
    have hsub : Finset.Iic i ⊆ ({k : Fin n | a k = (1:ℤ)} : Finset (Fin n)) := by
      intro k hk
      rw [Finset.mem_Iic] at hk
      have := ha hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases h01 k with h | h
      · rw [h, hi] at this; norm_num at this
      · exact h
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic, hj] at this
    omega
  · intro hi
    rcases h01 i with h | h
    · exfalso
      have hsub : ({k : Fin n | a k = (1:ℤ)} : Finset (Fin n)) ⊆ Finset.Iio i := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        rw [Finset.mem_Iio]
        by_contra hle
        push_neg at hle
        have := ha hle
        rw [h, hk] at this; norm_num at this
      have := Finset.card_le_card hsub
      rw [Fin.card_Iio, hj] at this
      omega
    · exact h

end GlobalTheory.ClosedSubgroupCriterion

import Mathlib

namespace GlobalTheory.PositiveIffLtCard

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs or assume the hypotheses.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem pos_iff_lt_card {N : ℕ} {e : Fin N → ℤ} (he : Antitone e) (i : Fin N) :
    (0 : ℤ) < e i ↔ (i : ℕ) < Finset.card {j : Fin N | (0 : ℤ) < e j} := by
  constructor
  · intro h
    have hsub : Finset.Iic i ⊆ ({j : Fin N | (0 : ℤ) < e j} : Finset (Fin N)) := by
      intro j hj
      rw [Finset.mem_Iic] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_lt_of_le h (he hj)
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hc
    omega
  · intro h
    by_contra hn
    have hsub : ({j : Fin N | (0 : ℤ) < e j} : Finset (Fin N)) ⊆ Finset.Iio i := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [Finset.mem_Iio]
      by_contra hji
      exact hn (lt_of_lt_of_le hj (he (not_lt.mp hji)))
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hc
    omega

end GlobalTheory.PositiveIffLtCard

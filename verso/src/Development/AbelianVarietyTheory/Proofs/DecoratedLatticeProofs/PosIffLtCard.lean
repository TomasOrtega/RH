import Mathlib

namespace GlobalTheory.PositiveIffLtCard

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hsub : Finset.Iic i ⊆ ({j : Fin N | (0 : ℤ) < e j} : Finset (Fin N))`. Introduce `j hj`. Rewrite `hj` using `[Finset.mem_Iic]`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `lt_of_lt_of_le h (he hj)`. Establish `hc` using `Finset.card_le_card hsub`. Rewrite `hc` using `[Fin.card_Iic]`. Use linear arithmetic over natural numbers and integers.

Introduce `h`. Assume the negation of the conclusion as `hn`. Establish `hsub : ({j : Fin N | (0 : ℤ) < e j} : Finset (Fin N)) ⊆ Finset.Iio i`. Introduce `j hj`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hj`.

Rewrite using `[Finset.mem_Iio]`. Assume the negation of the conclusion as `hji`. Conclude with `hn (lt_of_lt_of_le hj (he (not_lt.mp hji)))`. Establish `hc` using `Finset.card_le_card hsub`. Rewrite `hc` using `[Fin.card_Iio]`.

Use linear arithmetic over natural numbers and integers.
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

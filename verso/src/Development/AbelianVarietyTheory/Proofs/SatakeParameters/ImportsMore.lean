import Mathlib

namespace GlobalTheory.ClosedSubgroupCriterion

/- English proof (translation)
Introduce `n j a ha h01 hj i`. Prove the components needed by the constructor for the conclusion. Introduce `hi`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`.

Establish `hsub : Finset.Iic i ⊆ ({k : Fin n | a k = (1:ℤ)} : Finset (Fin n))`. Introduce `k hk`. Rewrite `hk` using `[Finset.mem_Iic]`. Use `ha hk` as an intermediate fact. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`.

Break down `h01 k with h | h` into its components or cases. Rewrite `this` using `[h, hi]`. Evaluate the numerical expressions using `at this`. Conclude with `h`. Use `Finset.card_le_card hsub` as an intermediate fact.

Rewrite `this` using `[Fin.card_Iic, hj]`. Use linear arithmetic over natural numbers and integers. Introduce `hi`. Break down `h01 i with h | h` into its components or cases. It suffices to derive a contradiction.

Establish `hsub : ({k : Fin n | a k = (1:ℤ)} : Finset (Fin n)) ⊆ Finset.Iio i`. Introduce `k hk`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hk`. Rewrite using `[Finset.mem_Iio]`. Assume the negation of the conclusion as `hle`.

Use `push_neg at hle`. Use `ha hle` as an intermediate fact. Rewrite `this` using `[h, hk]`. Evaluate the numerical expressions using `at this`. Use `Finset.card_le_card hsub` as an intermediate fact.

Rewrite `this` using `[Fin.card_Iio, hj]`. Use linear arithmetic over natural numbers and integers. Conclude with `h`.
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

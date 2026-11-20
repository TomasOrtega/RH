import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.Reformulated.B.DYlb8.main :
    ∀ {n : ℕ} {S : Finset (Fin n)}, (∀ (a b : Fin n), b ≤ a → a ∈ S → b ∈ S) → ∀ (a : Fin n), a ∈ S ↔ (↑a : ℕ) < S.card := by
  intro n S h a
  constructor
  · intro ha
    have hsub : Finset.Iic a ⊆ S := fun b hb => h a b (Finset.mem_Iic.mp hb) ha
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    omega
  · intro hlt
    by_contra ha
    have hsub : S ⊆ Finset.Iio a :=
      fun b hb => Finset.mem_Iio.mpr (lt_of_not_ge fun hab => ha (h b a hab hb))
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    omega

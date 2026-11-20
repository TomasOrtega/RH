import Mathlib

/- English proof (translation)
Introduce `n S h a`. Prove the components needed by the constructor for the conclusion. Introduce `ha`. Establish `hsub : Finset.Iic a ⊆ S` using `fun b hb => h a b (Finset.mem_Iic.mp hb) ha`. Establish `hcard` using `Finset.card_le_card hsub`.

Rewrite `hcard` using `[Fin.card_Iic]`. Use linear arithmetic over natural numbers and integers. Introduce `hlt`. Assume the negation of the conclusion as `ha`. Establish `hsub : S ⊆ Finset.Iio a` using `fun b hb => Finset.mem_Iio.mpr (lt_of_not_ge fun hab => ha (h b a hab hb))`.

Establish `hcard` using `Finset.card_le_card hsub`. Rewrite `hcard` using `[Fin.card_Iio]`. Use linear arithmetic over natural numbers and integers.
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

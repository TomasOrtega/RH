import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.GlobalTheory
import Mathlib

namespace Bl.general_b_fact_upper_bis_form

/- English proof (translation)
Introduce `n f hmono i`. Unfold `PI.FJM.nP`. Prove the components needed by the constructor for the conclusion. Introduce `hi`. Establish `hsub : Finset.Iic i ⊆ Finset.filter (fun j => 0 < f j) Finset.univ`.

Introduce `j hj`. Simplify using `only [Finset.mem_Iic] at hj`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Break down `lt_or_eq_of_le hj with h | h` into its components or cases. Conclude with `hmono j i h hi`.

Rewrite using `[h]`. Conclude with `hi`. Establish `hc` using `Finset.card_le_card hsub`. Rewrite `hc` using `[Fin.card_Iic]`. Use linear arithmetic over natural numbers and integers.

Introduce `hi`. Assume the negation of the conclusion as `hneg`. Establish `hsub : Finset.filter (fun j => 0 < f j) Finset.univ ⊆ Finset.Iio i`. Introduce `j hj`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hj`.

Simplify using `only [Finset.mem_Iio]`. Assume the negation of the conclusion as `hji`. Rewrite `hji` using `[not_lt]`. Break down `lt_or_eq_of_le hji with h | h` into its components or cases. Conclude with `hneg (hmono i j h hj)`.

Conclude with `hneg (by rw [h]; exact hj)`. Establish `hc` using `Finset.card_le_card hsub`. Rewrite `hc` using `[Fin.card_Iio]`. Use linear arithmetic over natural numbers and integers.
-/
theorem goal1 :
  ∀ {n : Nat} (f : Fin n → Rat),
  (∀ (i i' : Fin n), LT.lt.{0} i i' → LT.lt.{0} 0 (f i') → LT.lt.{0} 0 (f i)) →
    ∀ (i : Fin n), Iff (LT.lt.{0} 0 (f i)) (LT.lt.{0} i.val (PI.FJM.nP f))  := by
  intro n f hmono i
  unfold PI.FJM.nP
  constructor
  · intro hi
    have hsub : Finset.Iic i ⊆ Finset.filter (fun j => 0 < f j) Finset.univ := by
      intro j hj
      simp only [Finset.mem_Iic] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases lt_or_eq_of_le hj with h | h
      · exact hmono j i h hi
      · rw [h]; exact hi
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hc
    omega
  · intro hi
    by_contra hneg
    have hsub : Finset.filter (fun j => 0 < f j) Finset.univ ⊆ Finset.Iio i := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [Finset.mem_Iio]
      by_contra hji
      rw [not_lt] at hji
      rcases lt_or_eq_of_le hji with h | h
      · exact hneg (hmono i j h hj)
      · exact hneg (by rw [h]; exact hj)
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hc
    omega

end Bl.general_b_fact_upper_bis_form

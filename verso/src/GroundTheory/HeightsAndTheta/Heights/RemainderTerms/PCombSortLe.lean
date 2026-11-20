import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Equiv

/- English proof (translation)
Introduce `m u l σ hl hul hu k`. Choose the witnesses or unpack the hypotheses as in `⟨j, hjk, hkj⟩ : ∃ j : Fin m, j ≤ k ∧ k ≤ σ j := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `hcard : (Iic k).card ≤ (Iio k).card`.

Use `card_le_card_of_injOn σ ?_ σ.injective.injOn` and prove the remaining obligations. Introduce `j hj`. Simplify using `only [coe_Iic, coe_Iio, Set.mem_Iic, Set.mem_Iio] at hj ⊢`. Conclude with `h j hj`. Rewrite `hcard` using `[Fin.card_Iic, Fin.card_Iio]`.

Use linear arithmetic over natural numbers and integers. Combine the equalities or inequalities in the displayed calculation.
-/
theorem CombSortLe.proof : CombSortLe.Statement := by
  intro m u l σ hl hul hu k
  obtain ⟨j, hjk, hkj⟩ : ∃ j : Fin m, j ≤ k ∧ k ≤ σ j := by
    by_contra h
    push Not at h
    have hcard : (Iic k).card ≤ (Iio k).card := by
      refine card_le_card_of_injOn σ ?_ σ.injective.injOn
      intro j hj
      simp only [coe_Iic, coe_Iio, Set.mem_Iic, Set.mem_Iio] at hj ⊢
      exact h j hj
    rw [Fin.card_Iic, Fin.card_Iio] at hcard
    omega
  calc u (σ k) ≤ u (σ j) := hu hjk
    _ ≤ l (σ j) := hul _
    _ ≤ l k := hl hkj

end GroundTheory.Heights₂.Heights.RestTerms

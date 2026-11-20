import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

/- English proof (translation)
Introduce `k l hlt hinj`. Establish `hsplit : ∀ i, l i = l i % k + k * (if k ≤ l i then 1 else 0)`. Introduce `i`. Establish `hi` using `hlt i`. Use `split_ifs with h`.

Rewrite using `[Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Nat.mod_eq_of_lt (by omega)]`. Use linear arithmetic over natural numbers and integers. Establish `himg : (univ.image fun i => l i % k) = range k`.

Apply `Finset.eq_of_subset_of_card_le` to reduce the goal to its premises. Introduce `c hc`. Simplify using `only [mem_image, mem_univ, true_and] at hc`. Take `⟨i, rfl⟩` from `hc`. Conclude with `mem_range.2 (Nat.mod_lt _ i.pos)`.

Rewrite using `[card_image_of_injective _ hinj, card_range, card_univ, Fintype.card_fin]`. Establish `hres : ∑ i, l i % k = k * (k - 1) / 2`. Rewrite using `[← sum_range_id, ← himg, sum_image (fun i _ j _ h => hinj h)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[sum_add_distrib, ← mul_sum, sum_boole, Nat.cast_id]`.

Use `_ = k * (k - 1) / 2 + k * (univ.filter fun i => k ≤ l i).card := by`. Rewrite using `[hres]`.
-/
theorem SchResidueCount.proof : SchResidueCount.Statement := by
  intro k l hlt hinj
  have hsplit : ∀ i, l i = l i % k + k * (if k ≤ l i then 1 else 0) := by
    intro i
    have hi := hlt i
    split_ifs with h
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega
  have himg : (univ.image fun i => l i % k) = range k := by
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      simp only [mem_image, mem_univ, true_and] at hc
      obtain ⟨i, rfl⟩ := hc
      exact mem_range.2 (Nat.mod_lt _ i.pos)
    · rw [card_image_of_injective _ hinj, card_range, card_univ, Fintype.card_fin]
  have hres : ∑ i, l i % k = k * (k - 1) / 2 := by
    rw [← sum_range_id, ← himg, sum_image (fun i _ j _ h => hinj h)]
  calc ∑ i, l i = ∑ i, (l i % k + k * (if k ≤ l i then 1 else 0)) :=
        sum_congr rfl (fun i _ => hsplit i)
    _ = ∑ i, l i % k + k * (univ.filter fun i => k ≤ l i).card := by
        rw [sum_add_distrib, ← mul_sum, sum_boole, Nat.cast_id]
    _ = k * (k - 1) / 2 + k * (univ.filter fun i => k ≤ l i).card := by
        rw [hres]

end GroundTheory.Heights₂.Heights.RestTerms

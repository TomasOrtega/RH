import Formalism.WachLatticeTwists.Statement

open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem card_filter_add_le_of_none {α : Type*} (p : α → Prop) [DecidablePred p]
    (s t : Multiset α) (hs : ∀ u ∈ s, ¬ p u) :
    Multiset.card ((s + t).filter p) ≤ Multiset.card t := by
  rw [Multiset.filter_add, Multiset.filter_eq_nil.2 hs, zero_add]
  exact Multiset.card_le_card (Multiset.filter_le _ _)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the relevant objects with their definitions. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem jumpsColumn : Formalism.RepresentationBoundsCohomology.StatJumpsColumn := by
  intro ι _ cloud lows m j h0 hc hl hj hh
  have hτ : ∀ τ, negCount (cloud τ + lows τ) ≤ m := fun τ => by
    unfold negCount
    exact (card_filter_add_le_of_none _ _ _ fun u hu => not_lt.2 (hc τ u hu).le).trans (hl τ)
  calc j = ∑ τ, negCount (cloud τ + lows τ) := by rw [hj, hh, zero_add]
    _ ≤ ∑ _τ : ι, m := Finset.sum_le_sum fun τ _ => hτ τ
    _ = Fintype.card ι * m := by simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities.

Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem jumpsRow : Formalism.RepresentationBoundsCohomology.StatJumpsRow := by
  intro ι _ cloud lows m j h0 hc hl hj hh
  have hτ : ∀ τ, negCount ((cloud τ + lows τ).map (fun u => -u - 1)) ≤ m := fun τ => by
    unfold negCount
    rw [Multiset.map_add]
    refine (card_filter_add_le_of_none _ _ _ ?_).trans ?_
    · intro v hv
      obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.1 hv
      have := hc τ u hu
      omega
    · rw [Multiset.card_map]
      exact hl τ
  calc j = ∑ τ, negCount ((cloud τ + lows τ).map (fun u => -u - 1)) := by rw [hj, hh, zero_add]
    _ ≤ ∑ _τ : ι, m := Finset.sum_le_sum fun τ _ => hτ τ
    _ = Fintype.card ι * m := by simp

end Formalism.RepresentationBoundsCohomology

import Formalism.WachLatticeTwists.Statement

open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology

/- English proof (translation)
Rewrite using `[Multiset.filter_add, Multiset.filter_eq_nil.2 hs, zero_add]`. Conclude with `Multiset.card_le_card (Multiset.filter_le _ _)`.
-/
theorem card_filter_add_le_of_none {α : Type*} (p : α → Prop) [DecidablePred p]
    (s t : Multiset α) (hs : ∀ u ∈ s, ¬ p u) :
    Multiset.card ((s + t).filter p) ≤ Multiset.card t := by
  rw [Multiset.filter_add, Multiset.filter_eq_nil.2 hs, zero_add]
  exact Multiset.card_le_card (Multiset.filter_le _ _)

/- English proof (translation)
Introduce `ι _ cloud lows m j h0 hc hl hj hh`. Establish `hτ : ∀ τ, negCount (cloud τ + lows τ) ≤ m` using `fun τ => by`. Unfold `negCount`. Conclude with `(card_filter_add_le_of_none _ _ _ fun u hu => not_lt.2 (hc τ u hu).le).trans (hl τ)`. Combine the equalities or inequalities in the displayed calculation.
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
Introduce `ι _ cloud lows m j h0 hc hl hj hh`. Establish `hτ : ∀ τ, negCount ((cloud τ + lows τ).map (fun u => -u - 1)) ≤ m` using `fun τ => by`. Unfold `negCount`. Rewrite using `[Multiset.map_add]`. Use `(card_filter_add_le_of_none _ _ _ ?_).trans ?_` and prove the remaining obligations.

Introduce `v hv`. Take `⟨u, hu, rfl⟩` from `Multiset.mem_map.1 hv`. Use `hc τ u hu` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[Multiset.card_map]`.

Conclude with `hl τ`. Combine the equalities or inequalities in the displayed calculation.
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

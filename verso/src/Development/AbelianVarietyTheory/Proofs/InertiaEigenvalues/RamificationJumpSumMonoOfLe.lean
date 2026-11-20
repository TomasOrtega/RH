import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

open Classical in

/- English proof (translation)
Introduce `G _ R A B C hR ⟨m, hm⟩ hBC`. Establish `hbot : ∀ t, m ≤ t → ∀ D : Subgroup G, A ⊓ R t ≤ D`. Introduce `t ht D`. Establish `: R t ≤ ⊥` using `hm ▸ hR ht`. Conclude with `le_trans inf_le_right (le_trans this bot_le)`.

Establish `hfin : ∀ D : Subgroup G, (Function.support fun t : ℕ => if A ⊓ R t ≤ D then 0 else Nat.card ↥(A ⊓ R t)) ⊆ ↑(Finset.range m)`. Introduce `D`. Introduce `t ht`. Simplify using `only [Finset.coe_range, Set.mem_Iio]`. Assume the negation of the conclusion as `h`.

Apply `ht` to reduce the goal to its premises. Simplify using `[hbot t (not_lt.mp h) D]`. Unfold `jumpSum`. Rewrite using `[finsum_eq_sum_of_support_subset _ (hfin B), finsum_eq_sum_of_support_subset _ (hfin C)]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `t _`. Distinguish the cases in `hC : A ⊓ R t ≤ C`. Simplify using `[hBC t hC]`. Apply the tactic sequence `rw [if_neg hC] split_ifs <;> simp`.
-/
theorem jumpSum_mono_of_le :
    ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B C : Subgroup G), Antitone R → (∃ m, R m = ⊥) →
      (∀ t, A ⊓ R t ≤ C → A ⊓ R t ≤ B) → jumpSum R A B ≤ jumpSum R A C := by
  intro G _ R A B C hR ⟨m, hm⟩ hBC
  have hbot : ∀ t, m ≤ t → ∀ D : Subgroup G, A ⊓ R t ≤ D := by
    intro t ht D
    have : R t ≤ ⊥ := hm ▸ hR ht
    exact le_trans inf_le_right (le_trans this bot_le)
  have hfin : ∀ D : Subgroup G,
      (Function.support fun t : ℕ => if A ⊓ R t ≤ D then 0 else Nat.card ↥(A ⊓ R t)) ⊆ ↑(Finset.range m) := by
    intro D
    intro t ht
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply ht
    simp [hbot t (not_lt.mp h) D]
  unfold jumpSum
  rw [finsum_eq_sum_of_support_subset _ (hfin B), finsum_eq_sum_of_support_subset _ (hfin C)]
  apply Finset.sum_le_sum
  intro t _
  by_cases hC : A ⊓ R t ≤ C
  · simp [hBC t hC]
  · rw [if_neg hC]
    split_ifs <;> simp

end GlobalTheory.PMon.Ram

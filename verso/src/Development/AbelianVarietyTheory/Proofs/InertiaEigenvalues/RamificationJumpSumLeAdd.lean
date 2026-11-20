import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

/- English proof (translation)
Introduce `t ht`. Simplify using `only [Finset.coe_range, Set.mem_Iio]`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `ht` to reduce the goal to its premises.

Establish `h1 : R t = ⊥` using `le_bot_iff.mp (hm ▸ hR h)`. Simplify using `[h1]`.
-/
theorem jumpSum_support_subset {G : Type} [Group G] (R : ℕ → Subgroup G) (A B : Subgroup G) (hR : Antitone R)
    (m : ℕ) (hm : R m = ⊥) :
    Function.support (fun t : ℕ => by classical exact if A ⊓ R t ≤ B then 0 else Nat.card ↥(A ⊓ R t)) ⊆
      ↑(Finset.range m) := by
  classical
  intro t ht
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  push_neg at h
  apply ht
  have h1 : R t = ⊥ := le_bot_iff.mp (hm ▸ hR h)
  simp [h1]

/- English proof (translation)
Introduce `G _ R A B C hR ⟨m, hm⟩ hBA`. Unfold `jumpSum`. Rewrite using `[finsum_eq_sum_of_support_subset _ (jumpSum_support_subset R A C hR m hm), finsum_eq_sum_of_support_subset _ (jumpSum_support_subset R A B hR m hm), finsum_eq_sum_of_support_subset _ (jumpSum_support_subset R B C hR m hm), ← Finset.sum_add_distrib]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `t _`.

Distinguish the cases in `hC : A ⊓ R t ≤ C`. Simplify using `[hC]`. Distinguish the cases in `hB : A ⊓ R t ≤ B`. Establish `heq : B ⊓ R t = A ⊓ R t` using `le_antisymm (inf_le_inf_right _ hBA) (le_inf hB inf_le_right)`. Establish `hC' : ¬ B ⊓ R t ≤ C` using `by rw [heq]; exact hC`.

Simplify using `[hC, hC', heq]`. Simplify using `[hC, hB]`.
-/
theorem jumpSum_le_add : ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B C : Subgroup G), Antitone R →
    (∃ m, R m = ⊥) → B ≤ A → jumpSum R A C ≤ jumpSum R A B + jumpSum R B C := by
  intro G _ R A B C hR ⟨m, hm⟩ hBA
  classical
  unfold jumpSum
  rw [finsum_eq_sum_of_support_subset _ (jumpSum_support_subset R A C hR m hm),
    finsum_eq_sum_of_support_subset _ (jumpSum_support_subset R A B hR m hm),
    finsum_eq_sum_of_support_subset _ (jumpSum_support_subset R B C hR m hm),
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t _
  by_cases hC : A ⊓ R t ≤ C
  · simp [hC]
  · by_cases hB : A ⊓ R t ≤ B
    · have heq : B ⊓ R t = A ⊓ R t :=
        le_antisymm (inf_le_inf_right _ hBA) (le_inf hB inf_le_right)
      have hC' : ¬ B ⊓ R t ≤ C := by rw [heq]; exact hC
      simp [hC, hC', heq]
    · simp [hC, hB]

end GlobalTheory.PMon.Ram

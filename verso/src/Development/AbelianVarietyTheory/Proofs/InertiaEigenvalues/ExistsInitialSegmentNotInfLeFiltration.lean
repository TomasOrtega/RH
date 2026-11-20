import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

/- English proof (translation)
Introduce `G _ R A B hR hm`. Take `⟨m, hm⟩` from `hm`. Establish `h : ∃ t, A ⊓ R t ≤ B` using `⟨m, by rw [hm]; simp⟩`. Use `⟨Nat.find h, fun t => ⟨fun ht => Nat.find_min h ht, fun hn => ?_⟩⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `hn (le_trans (inf_le_inf_left A (hR hc)) (Nat.find_spec h))`.
-/
theorem exists_initialSegment_not_inf_le :
    ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B : Subgroup G), Antitone R →
      (∃ m, R m = ⊥) → ∃ n : ℕ, ∀ t, t < n ↔ ¬ A ⊓ R t ≤ B := by
  intro G _ R A B hR hm
  classical
  obtain ⟨m, hm⟩ := hm
  have h : ∃ t, A ⊓ R t ≤ B := ⟨m, by rw [hm]; simp⟩
  refine ⟨Nat.find h, fun t => ⟨fun ht => Nat.find_min h ht, fun hn => ?_⟩⟩
  by_contra hc
  push_neg at hc
  exact hn (le_trans (inf_le_inf_left A (hR hc)) (Nat.find_spec h))

end GlobalTheory.PMon.Ram

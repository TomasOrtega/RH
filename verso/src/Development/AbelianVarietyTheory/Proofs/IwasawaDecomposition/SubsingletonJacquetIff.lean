import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.CuspEntries

/- English proof (translation)
Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem blk_two_stdSum {r t N : ℕ} (h : r + t = N) (a : Fin N) :
    blk (two (stdSum h)) a = decide (r ≤ (a : ℕ)) := by
  obtain ⟨a, rfl⟩ := (stdSum h).surjective a
  rcases a with a | a
  · rw [← two_false, blk_apply, two_false]
    simp [stdSum]
  · rw [← two_true, blk_apply, two_true]
    simp [stdSum]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem mem_unipRad_two_stdSum {R : Type} [CommRing R] {r t N : ℕ} (h : r + t = N) (u : GL (Fin N) R) :
    u ∈ unipRad R (two (stdSum h)) ↔ ∀ a b : Fin N, ¬ ((a : ℕ) < r ∧ r ≤ (b : ℕ)) →
      (u : Matrix (Fin N) (Fin N) R) a b = (1 : Matrix (Fin N) (Fin N) R) a b := by
  rw [CuspMax.mem_unipRad_iff_entries]
  refine forall₂_congr fun a b => imp_congr_left (not_congr ?_)
  rw [blk_two_stdSum, blk_two_stdSum]
  by_cases h1 : r ≤ (a : ℕ) <;> by_cases h2 : r ≤ (b : ℕ) <;> simp [h1, h2] <;> omega

end GlobalTheory.CuspEntries

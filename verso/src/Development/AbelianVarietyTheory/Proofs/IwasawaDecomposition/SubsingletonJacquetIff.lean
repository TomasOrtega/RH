import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.CuspEntries

/- English proof (translation)
Take `⟨a, rfl⟩` from `(stdSum h).surjective a`. Break down `a with a | a` into its components or cases. Rewrite using `[← two_false, blk_apply, two_false]`. Simplify using `[stdSum]`. Rewrite using `[← two_true, blk_apply, two_true]`.

Simplify using `[stdSum]`.
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
Rewrite using `[CuspMax.mem_unipRad_iff_entries]`. Use `forall₂_congr fun a b => imp_congr_left (not_congr ?_)` and prove the remaining obligations. Rewrite using `[blk_two_stdSum, blk_two_stdSum]`. Apply the tactic sequence `by_cases h1 : r ≤ (a : ℕ) <;> by_cases h2 : r ≤ (b : ℕ) <;> simp [h1, h2] <;> omega`.
-/
theorem mem_unipRad_two_stdSum {R : Type} [CommRing R] {r t N : ℕ} (h : r + t = N) (u : GL (Fin N) R) :
    u ∈ unipRad R (two (stdSum h)) ↔ ∀ a b : Fin N, ¬ ((a : ℕ) < r ∧ r ≤ (b : ℕ)) →
      (u : Matrix (Fin N) (Fin N) R) a b = (1 : Matrix (Fin N) (Fin N) R) a b := by
  rw [CuspMax.mem_unipRad_iff_entries]
  refine forall₂_congr fun a b => imp_congr_left (not_congr ?_)
  rw [blk_two_stdSum, blk_two_stdSum]
  by_cases h1 : r ≤ (a : ℕ) <;> by_cases h2 : r ≤ (b : ℕ) <;> simp [h1, h2] <;> omega

end GlobalTheory.CuspEntries

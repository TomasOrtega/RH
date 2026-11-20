import Mathlib

namespace GlobalTheory.CompanionTheory.FinReversal

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem prod_filter_le_rev {M : Type*} [CommMonoid M] (h : ℕ) (f : Fin h → M) (j : Fin h) :
    ∏ a ∈ Finset.univ.filter (fun a => a ≤ j), f (Fin.rev a)
      = ∏ i ∈ Finset.univ.filter (fun i => Fin.rev j ≤ i), f i := by
  refine Finset.prod_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact Fin.rev_le_rev.mpr ha
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [← Fin.rev_le_rev, Fin.rev_rev]
    exact ha
  · intro a _
    exact Fin.rev_rev a
  · intro a _
    exact Fin.rev_rev a
  · intro a _
    rfl

end GlobalTheory.CompanionTheory.FinReversal

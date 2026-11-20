import Mathlib

namespace GlobalTheory.CompanionTheory.FinReversal

/- English proof (translation)
Use `Finset.prod_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `a ha`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢`. Conclude with `Fin.rev_le_rev.mpr ha`. Introduce `a ha`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢`. Rewrite using `[← Fin.rev_le_rev, Fin.rev_rev]`. Conclude with `ha`. Introduce `a _`. Conclude with `Fin.rev_rev a`.

Introduce `a _`. Conclude with `Fin.rev_rev a`. Introduce `a _`. Both sides reduce to the same expression.
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

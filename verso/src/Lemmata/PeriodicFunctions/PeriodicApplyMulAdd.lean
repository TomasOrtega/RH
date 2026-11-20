import Mathlib

open NumberField IsDedekindDomain Module

namespace Bl.PeriodicFunctions

variable {K : Type} [Field K]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the hypotheses and the conclusion using the stated equalities.
-/
private theorem periodic_apply_mul_add (M : ℕ) (g : ℕ → K) (hg : ∀ i, g (i + M) = g i) (k x : ℕ) :
    g (M * k + x) = g x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, show M * k + M + x = (M * k + x) + M by ring, hg, ih]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem goal1 (M m : ℕ) (g : ℕ → K) (hg : ∀ i, g (i + M) = g i) :
    ∑ i ∈ Finset.range (M * m), g i = (m : K) * ∑ i ∈ Finset.range M, g i := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp only [periodic_apply_mul_add M g hg n]
    push_cast
    ring

end Bl.PeriodicFunctions

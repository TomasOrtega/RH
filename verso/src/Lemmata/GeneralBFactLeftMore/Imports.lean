import Mathlib

open MvPolynomial IsLocalRing

namespace Bl.general_b_fact_left_more

variable {n : ℕ}

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Treat this case separately. Establish an intermediate fact. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem goal1 (p : Fin n → ℂ) (a : MvPolynomial (Fin n) ℂ) :
    a - C (eval p a) ∈ Ideal.span (Set.range fun i => X i - C (p i)) := by
  induction a using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg =>
    have h : f + g - C (eval p (f + g)) = (f - C (eval p f)) + (g - C (eval p g)) := by
      simp only [map_add]; ring
    rw [h]
    exact Ideal.add_mem _ hf hg
  | mul_X f i hf =>
    have h : f * X i - C (eval p (f * X i)) =
        (f - C (eval p f)) * X i + C (eval p f) * (X i - C (p i)) := by
      simp only [map_mul, eval_X]; ring
    rw [h]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hf) (Ideal.mul_mem_left _ _ ?_)
    exact Ideal.subset_span ⟨i, rfl⟩

end Bl.general_b_fact_left_more

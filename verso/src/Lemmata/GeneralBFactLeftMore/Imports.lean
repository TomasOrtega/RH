import Mathlib

open MvPolynomial IsLocalRing

namespace Bl.general_b_fact_left_more

variable {n : ℕ}

/- English proof (translation)
Proceed by induction on `a using MvPolynomial.induction_on with`. Consider the case `C c => simp`. Consider the case `add f g hf hg`. Establish `h : f + g - C (eval p (f + g)) = (f - C (eval p f)) + (g - C (eval p g))`. Simplify using `only [map_add]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`. Conclude with `Ideal.add_mem _ hf hg`. Consider the case `mul_X f i hf`. Establish `h : f * X i - C (eval p (f * X i)) = (f - C (eval p f)) * X i + C (eval p f) * (X i - C (p i))`.

Simplify using `only [map_mul, eval_X]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`. Use `Ideal.add_mem _ (Ideal.mul_mem_right _ _ hf) (Ideal.mul_mem_left _ _ ?_)` and prove the remaining obligations. Conclude with `Ideal.subset_span ⟨i, rfl⟩`.
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

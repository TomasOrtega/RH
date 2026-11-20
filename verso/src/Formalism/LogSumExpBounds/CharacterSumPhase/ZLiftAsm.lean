import Formalism.LogSumExpBounds.StatementZ

namespace Formalism.NuclearRankWeightBounds.P

open Finset

noncomputable def sz {f : ℕ} (x : Fin f → ℝ) (K : ℕ) (z : Fin f → ℂ) (a : ℝ) : ℝ :=
  ∑ A ∈ (univ : Finset (Fin f)).powerset, (∏ v ∈ A, (2 / (x v * ‖z v‖)) ^ (2 * K)) * a ^ 2

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Check the signs of the components of the expression.
-/
lemma sz_nonneg {f : ℕ} (x : Fin f → ℝ) (K : ℕ) (z : Fin f → ℂ) (a : ℝ) (hx : ∀ v, 0 < x v) :
    0 ≤ sz x K z a := by
  unfold sz
  refine sum_nonneg fun A _ => mul_nonneg (prod_nonneg fun v _ => ?_) (sq_nonneg _)
  have := hx v
  positivity

end Formalism.NuclearRankWeightBounds.P

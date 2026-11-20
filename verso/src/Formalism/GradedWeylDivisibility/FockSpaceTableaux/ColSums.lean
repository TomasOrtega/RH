import Formalism.GradedWeylDivisibility.StatementC

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `[colW, Pi.single_apply]`.
-/
theorem lccomp_weight_colW_apply {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (t : Fin n) :
    (Finsupp.weight (colW r n) m) t = ∑ a : Fin r, m (a, t) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [colW, Pi.single_apply]

/- English proof (translation)
Introduce `R _ r n ν f hf m hm t`. Establish `h1` using `(Submodule.mem_inf.mp hf).1`. Rewrite `h1` using `[mem_weightedHomogeneousSubmodule]`. Rewrite using `[← lccomp_weight_colW_apply, h1 (mem_support_iff.mp hm)]`.
-/
theorem columnSums_holds : ColSums := by
  intro R _ r n ν f hf m hm t
  have h1 := (Submodule.mem_inf.mp hf).1
  rw [mem_weightedHomogeneousSubmodule] at h1
  rw [← lccomp_weight_colW_apply, h1 (mem_support_iff.mp hm)]

end Formalism.GradedWeylDivisibility

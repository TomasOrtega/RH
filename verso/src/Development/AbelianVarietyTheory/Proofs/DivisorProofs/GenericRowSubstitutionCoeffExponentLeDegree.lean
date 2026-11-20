import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeAevalLeOfDegLeOne

set_option autoImplicit false

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

namespace GlobalTheory.GenSubDeg

/- English proof (translation)
Introduce `O _ N D f hf m hm v`. Establish `hg : ∀ i : Fin N × Fin N, (∑ b : Fin N, (X (i.1, b) * C (X (b, i.2)) : MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O))).totalDegree ≤ 1`. Introduce `i`. Use `totalDegree_finsetSum_le fun b _ => ?_` and prove the remaining obligations. Use `(totalDegree_mul _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[totalDegree_C, add_zero]`. Rewrite using `[X]`. Conclude with `(totalDegree_monomial_le _ _).trans (by simp)`. Establish `hdeg` using `GlobalTheory.SZShift.totalDegree_aeval_le_of_deg_le_one _ hg f`. Establish `h1 : m.degree ≤ (GlobalTheory.HighWt.genSub O N f).totalDegree`.

Rewrite using `[Finsupp.degree]`. Conclude with `le_totalDegree (mem_support_iff.mpr hm)`. Establish `h2 : m v ≤ m.degree` using `by classical`. Rewrite using `[Finsupp.degree]`. Distinguish the cases in `hv : v ∈ m.support`.

Conclude with `Finset.single_le_sum (fun _ _ => Nat.zero_le _) hv`. Simplify using `[Finsupp.notMem_support_iff.mp hv]`. Conclude with `h2.trans (h1.trans ((hdeg.trans hf)))`.
-/
theorem genSub_coeff_le : ∀ (O : Type) [CommRing O] (N : ℕ) (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O), f.totalDegree ≤ D → ∀ m, (GlobalTheory.HighWt.genSub O N f).coeff m ≠ 0 → ∀ v, m v ≤ D := by
  intro O _ N D f hf m hm v
  have hg : ∀ i : Fin N × Fin N, (∑ b : Fin N, (X (i.1, b) * C (X (b, i.2)) : MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O))).totalDegree ≤ 1 := by
    intro i
    refine totalDegree_finsetSum_le fun b _ => ?_
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, add_zero]
    rw [X]
    exact (totalDegree_monomial_le _ _).trans (by simp)
  have hdeg := GlobalTheory.SZShift.totalDegree_aeval_le_of_deg_le_one _ hg f
  have h1 : m.degree ≤ (GlobalTheory.HighWt.genSub O N f).totalDegree := by
    rw [Finsupp.degree]
    exact le_totalDegree (mem_support_iff.mpr hm)
  have h2 : m v ≤ m.degree := by
    classical
    rw [Finsupp.degree]
    by_cases hv : v ∈ m.support
    · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hv
    · simp [Finsupp.notMem_support_iff.mp hv]
  exact h2.trans (h1.trans ((hdeg.trans hf)))

end GlobalTheory.GenSubDeg

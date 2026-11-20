import Mathlib

namespace GlobalTheory.AevalTotalDegreeLinear

open MvPolynomial

/- English proof (translation)
Use `conv_lhs => rw [P.as_sum]`. Rewrite using `[map_sum]`. Use `(totalDegree_finset_sum _ _).trans ?_` and prove the remaining obligations. Use `Finset.sup_le fun s hs => ?_` and prove the remaining obligations. Rewrite using `[aeval_monomial]`.

Use `(totalDegree_mul _ _).trans ?_` and prove the remaining obligations. Rewrite using `[algebraMap_eq, totalDegree_C, zero_add]`. Establish `hprod : totalDegree (s.prod fun i k => f i ^ k) ≤ s.sum fun _ k => k`. Rewrite using `[Finsupp.prod, Finsupp.sum]`. Use `(totalDegree_finset_prod _ _).trans ?_` and prove the remaining obligations.

Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Use `(totalDegree_pow _ _).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `hprod.trans ?_` and prove the remaining obligations. Conclude with `Finset.le_sup (f := fun s : κ →₀ ℕ => s.sum fun _ e => e) hs`.
-/
theorem totalDegree_aeval_le_of_linear {κ : Type} (f : κ → MvPolynomial κ ℂ)
    (hf : ∀ (i : κ), MvPolynomial.totalDegree (f i) ≤ (1 : ℕ)) (P : MvPolynomial κ ℂ) :
    MvPolynomial.totalDegree ((MvPolynomial.aeval f : MvPolynomial κ ℂ → MvPolynomial κ ℂ) P)
      ≤ MvPolynomial.totalDegree P := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine (totalDegree_finset_sum _ _).trans ?_
  refine Finset.sup_le fun s hs => ?_
  rw [aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [algebraMap_eq, totalDegree_C, zero_add]
  have hprod : totalDegree (s.prod fun i k => f i ^ k) ≤ s.sum fun _ k => k := by
    rw [Finsupp.prod, Finsupp.sum]
    refine (totalDegree_finset_prod _ _).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    refine (totalDegree_pow _ _).trans ?_
    calc s i * totalDegree (f i) ≤ s i * 1 := Nat.mul_le_mul_left _ (hf i)
      _ = s i := mul_one _
  refine hprod.trans ?_
  exact Finset.le_sup (f := fun s : κ →₀ ℕ => s.sum fun _ e => e) hs

/- English proof (translation)
Introduce `f hf P` and use `totalDegree_aeval_le_of_linear f hf P`.
-/
theorem main : ∀ {κ : Type} (f : κ → MvPolynomial κ ℂ), (∀ (i : κ), MvPolynomial.totalDegree (f i) ≤ (1 : ℕ)) → ∀ (P : MvPolynomial κ ℂ), MvPolynomial.totalDegree ((MvPolynomial.aeval f : MvPolynomial κ ℂ → MvPolynomial κ ℂ) P) ≤ MvPolynomial.totalDegree P :=
  fun f hf P => totalDegree_aeval_le_of_linear f hf P

end GlobalTheory.AevalTotalDegreeLinear

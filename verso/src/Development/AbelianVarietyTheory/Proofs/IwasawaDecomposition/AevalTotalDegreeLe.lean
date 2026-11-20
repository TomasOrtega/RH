import Mathlib
universe u_1
namespace GlobalTheory.AevalTotalDegreeBound
open MvPolynomial

/- English proof (translation)
Use `conv_lhs => rw [P.as_sum]`. Rewrite using `[map_sum]`. Use `(totalDegree_finset_sum _ _).trans ?_` and prove the remaining obligations. Use `Finset.sup_le fun s hs => ?_` and prove the remaining obligations. Rewrite using `[aeval_monomial, algebraMap_eq]`.

Use `(totalDegree_mul _ _).trans ?_` and prove the remaining obligations. Rewrite using `[totalDegree_C, zero_add]`. Use `le_trans ?_ (le_totalDegree hs)` and prove the remaining obligations. Unfold `Finsupp.prod`. Use `(totalDegree_finset_prod _ _).trans ?_` and prove the remaining obligations.

Unfold `Finsupp.sum`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Use `(totalDegree_pow _ _).trans ?_` and prove the remaining obligations. Simplify using `using Nat.mul_le_mul_left (s i) (hf i)`.
-/
theorem aeval_totalDegree_le {σ : Type u_1} (f : σ → MvPolynomial σ ℂ)
    (hf : ∀ v, (f v).totalDegree ≤ 1) (P : MvPolynomial σ ℂ) :
    (aeval f P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine (totalDegree_finset_sum _ _).trans ?_
  refine Finset.sup_le fun s hs => ?_
  rw [aeval_monomial, algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine le_trans ?_ (le_totalDegree hs)
  unfold Finsupp.prod
  refine (totalDegree_finset_prod _ _).trans ?_
  unfold Finsupp.sum
  refine Finset.sum_le_sum fun i _ => ?_
  refine (totalDegree_pow _ _).trans ?_
  simpa using Nat.mul_le_mul_left (s i) (hf i)

/- English proof (translation)
Introduce `f hf P` and use `aeval_totalDegree_le f hf P`.
-/
theorem main : ∀ {σ : Type u_1} (f : σ → MvPolynomial σ ℂ), (∀ (v : σ), MvPolynomial.totalDegree (f v) ≤ (1 : ℕ)) → ∀ (P : MvPolynomial σ ℂ), MvPolynomial.totalDegree ((MvPolynomial.aeval f : MvPolynomial σ ℂ → MvPolynomial σ ℂ) P) ≤ MvPolynomial.totalDegree P :=
  fun f hf P => aeval_totalDegree_le f hf P

end GlobalTheory.AevalTotalDegreeBound

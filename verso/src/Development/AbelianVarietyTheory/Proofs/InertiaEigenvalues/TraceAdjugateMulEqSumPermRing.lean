import Mathlib

open scoped BigOperators
open Polynomial Matrix

namespace GlobalTheory

/- English proof (translation)
Establish `h1 : ∀ i, (M.adjugate * B) i i = (M.updateCol i (fun k => B k i)).det`. Introduce `i`. Rewrite using `[← cramer_apply, cramer_eq_adjugate_mulVec]`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Simplify using `only [Matrix.trace, Matrix.diag, h1, det_apply']`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun σ _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Use `congr 1`.

Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]`. Simplify using `only [updateCol_apply]`. Rewrite using `[mul_comm]`. Use `congr 1`. Use `Finset.prod_congr rfl (fun j hj => ?_)` and prove the remaining obligations.

Rewrite using `[if_neg (Finset.ne_of_mem_erase hj)]`.
-/
theorem trace_adjugate_mul_eq_sum_perm_ring {A : Type} [CommRing A] {n : Type} [Fintype n]
    [DecidableEq n] (M B : Matrix n n A) :
    (M.adjugate * B).trace = ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : A) *
      ∑ i, (∏ j ∈ Finset.univ.erase i, M (σ j) j) * B (σ i) i := by
  have h1 : ∀ i, (M.adjugate * B) i i = (M.updateCol i (fun k => B k i)).det := by
    intro i
    rw [← cramer_apply, cramer_eq_adjugate_mulVec]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  simp only [Matrix.trace, Matrix.diag, h1, det_apply']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [updateCol_apply]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [if_neg (Finset.ne_of_mem_erase hj)]

/- English proof (translation)
Introduce `A _ n _ _ M₀ N`. Use `set P := (M₀.map C + (X : A[X]) • N.map C).det with hP`. Use `⟨P.divX.divX, ?_⟩` and prove the remaining obligations. Establish `h0 : P.coeff 0 = M₀.det`. Rewrite using `[coeff_zero_eq_eval_zero, hP, ← coe_evalRingHom, RingHom.map_det]`.

Use `congr 1`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Establish `h1 : P.coeff 1 = (M₀.adjugate * N).trace`. Establish `hd : P.coeff 1 = (derivative P).eval 0`.

Rewrite using `[← coeff_zero_eq_eval_zero, coeff_derivative]`. Simplify using the standard rewrite rules. Rewrite using `[hd, trace_adjugate_mul_eq_sum_perm_ring, hP, det_apply']`. Simplify using `[derivative_prod_finset, eval_finsetSum, eval_prod, Finset.mul_sum]`. Establish `e1` using `divX_mul_X_add P`.

Establish `e2` using `divX_mul_X_add P.divX`. Rewrite `e2` using `[coeff_divX, zero_add]`. Rewrite using `[← h0, ← h1]`. Take the linear combination `-e1 - X * e2`.
-/
theorem det_add_X_smul_first_variation : ∀ (A : Type) [CommRing A] (n : Type) [Fintype n]
    [DecidableEq n] (M₀ N : Matrix n n A), ∃ p : Polynomial A,
    (M₀.map Polynomial.C + (Polynomial.X : Polynomial A) • N.map Polynomial.C).det =
      Polynomial.C M₀.det + Polynomial.X * Polynomial.C (M₀.adjugate * N).trace +
        Polynomial.X ^ 2 * p := by
  intro A _ n _ _ M₀ N
  set P := (M₀.map C + (X : A[X]) • N.map C).det with hP
  refine ⟨P.divX.divX, ?_⟩
  have h0 : P.coeff 0 = M₀.det := by
    rw [coeff_zero_eq_eval_zero, hP, ← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp
  have h1 : P.coeff 1 = (M₀.adjugate * N).trace := by
    have hd : P.coeff 1 = (derivative P).eval 0 := by
      rw [← coeff_zero_eq_eval_zero, coeff_derivative]
      simp
    rw [hd, trace_adjugate_mul_eq_sum_perm_ring, hP, det_apply']
    simp [derivative_prod_finset, eval_finsetSum, eval_prod, Finset.mul_sum]
  have e1 := divX_mul_X_add P
  have e2 := divX_mul_X_add P.divX
  rw [coeff_divX, zero_add] at e2
  rw [← h0, ← h1]
  linear_combination -e1 - X * e2

end GlobalTheory

import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi

set_option autoImplicit false

open Polynomial

namespace UpperTheory.Gal.LocalSmoothExtension

/- English proof (translation)
Introduce `d n t c h hinj hc hEq i`. Use `set P : ℂ[X] := ∑ a ∈ Finset.range (d + 1), C ((-1) ^ a * t a) * X ^ a with hPdef`. Use `set Q : ℂ[X] := ∑ j, C c * X ^ (h j) with hQdef`. Establish `hPQ : P = Q`. Apply `Polynomial.funext` to reduce the goal to its premises.

Introduce `y`. Simplify using `only [hPdef, hQdef, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]`. Rewrite using `[← Finset.mul_sum, ← hEq y]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[neg_pow]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hQ : Q.coeff (h i) = c`. Simplify using `only [hQdef, finset_sum_coeff, coeff_C_mul, coeff_X_pow]`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules.

Introduce `j _ hji`. Rewrite using `[if_neg (fun e => hji (hinj e).symm), mul_zero]`. Introduce `hi`. Conclude with `absurd (Finset.mem_univ i) hi`. Establish `hP : P.coeff (h i) = if h i ∈ Finset.range (d + 1) then (-1) ^ (h i) * t (h i) else 0`.

Simplify using `only [hPdef, finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_ite_eq]`. Introduce `ht`. Rewrite `hP` using `[hPQ, hQ]`. Use `split_ifs at hP with hlt`.

Rewrite `hP` using `[ht, mul_zero]`. Conclude with `hc hP`. Conclude with `hc hP`.
-/
theorem coeffOcc_of : CoeffOcc := by
  intro d n t c h hinj hc hEq i
  set P : ℂ[X] := ∑ a ∈ Finset.range (d + 1), C ((-1) ^ a * t a) * X ^ a with hPdef
  set Q : ℂ[X] := ∑ j, C c * X ^ (h j) with hQdef
  have hPQ : P = Q := by
    apply Polynomial.funext
    intro y
    simp only [hPdef, hQdef, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
    rw [← Finset.mul_sum, ← hEq y]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [neg_pow]
    ring
  have hQ : Q.coeff (h i) = c := by
    simp only [hQdef, finset_sum_coeff, coeff_C_mul, coeff_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [if_neg (fun e => hji (hinj e).symm), mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hP : P.coeff (h i) = if h i ∈ Finset.range (d + 1) then (-1) ^ (h i) * t (h i) else 0 := by
    simp only [hPdef, finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
  intro ht
  rw [hPQ, hQ] at hP
  split_ifs at hP with hlt
  · rw [ht, mul_zero] at hP
    exact hc hP
  · exact hc hP

end UpperTheory.Gal.LocalSmoothExtension

import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit

open Finset MvPolynomial UpperTheory.Gal.Schur

/- English proof (translation)
Rewrite using `[← Finset.mul_prod_erase univ _ (mem_univ a), if_pos rfl]`. Use `congr 1`. Use `Finset.prod_congr rfl fun b hb => ?_` and prove the remaining obligations. Rewrite using `[if_neg (Finset.ne_of_mem_erase hb)]`.
-/
private theorem prod_ite_eq_mul_prod_erase {R : Type} [CommRing R] {n : ℕ} (d d' : Fin n → R) (a : Fin n) :
    ∏ b, (if b = a then d b else d' b) = d a * ∏ b ∈ univ.erase a, d' b := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ a), if_pos rfl]
  congr 1
  refine Finset.prod_congr rfl fun b hb => ?_
  rw [if_neg (Finset.ne_of_mem_erase hb)]

/- English proof (translation)
Introduce `R _ n M d d'`. Simplify using `only [Matrix.det_apply, Matrix.of_apply]`. Rewrite using `[Finset.sum_comm, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Simplify using `only [Finset.prod_mul_distrib, Units.smul_def, zsmul_eq_mul]`.

Establish `key : ∀ i, (∏ j, if j = i then d (σ j) else d' (σ j)) = ∏ b, (if b = σ i then d b else d' b)`. Introduce `i`. Rewrite using `[← Equiv.prod_comp σ (fun b => if b = σ i then d b else d' b)]`. Simplify using `only [σ.injective.eq_iff]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[key]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by`.

Use `congr 1`. Rewrite using `[Equiv.sum_comp σ (fun a => ∏ b, if b = a then d b else d' b)]`. Conclude with `Finset.sum_congr rfl fun a _ => prod_ite_eq_mul_prod_erase d d' a`.
-/
theorem UpperTheory.Gal.Schur.mixDet :
    MixDet := by
  intro R _ n M d d'
  simp only [Matrix.det_apply, Matrix.of_apply]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Finset.prod_mul_distrib, Units.smul_def, zsmul_eq_mul]
  have key : ∀ i, (∏ j, if j = i then d (σ j) else d' (σ j)) =
      ∏ b, (if b = σ i then d b else d' b) := by
    intro i
    rw [← Equiv.prod_comp σ (fun b => if b = σ i then d b else d' b)]
    simp only [σ.injective.eq_iff]
  calc _ = (∑ i, ∏ b, (if b = σ i then d b else d' b)) *
        ((Equiv.Perm.sign σ : ℤ) * ∏ x, M (σ x) x) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [key]
        ring
    _ = _ := by
        congr 1
        rw [Equiv.sum_comp σ (fun a => ∏ b, if b = a then d b else d' b)]
        exact Finset.sum_congr rfl fun a _ => prod_ite_eq_mul_prod_erase d d' a

import Mathlib

namespace GlobalTheory.UnitriangularLowerMulEq

open Matrix

/- English proof (translation)
Establish `hAb : A.BlockTriangular id` using `fun i j hji => hA i j hji`. Establish `hA'b : A'.BlockTriangular id` using `fun i j hji => hA' i j hji`. Establish `hdet : A.det = 1`. Rewrite using `[Matrix.det_of_isUpperTriangular hAb]`. Simplify using `[hA1]`.

Establish `hu : IsUnit A.det` using `by rw [hdet]; exact isUnit_one`. Establish `hLeq : L = A' * A⁻¹`. Rewrite using `[h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]`. Establish `: Invertible A` using `A.invertibleOfIsUnitDet hu`. Establish `hLb : L.BlockTriangular id` using `hLeq ▸ hA'b.mul (Matrix.blockTriangular_inv_of_blockTriangular hAb)`.

Establish `hoff : ∀ i j, i ≠ j → L i j = 0` using `fun i j hij => (lt_or_gt_of_ne hij).elim (hL i j) fun hji => hLb hji`. Establish `hdiag : ∀ i, L i i = 1`. Introduce `i`. Establish `hii` using `congrFun (congrFun h i) i`. Rewrite `hii` using `[Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hki => by rw [hoff i k (Ne.symm hki), zero_mul]) (by simp), hA1, mul_one, hA'1]`.

Conclude with `hii.symm`. Establish `hL1 : L = 1`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using `[hdiag]`. Simplify using `[hoff i j hij, Matrix.one_apply_ne hij]`. Rewrite using `[h, hL1, Matrix.one_mul]`.
-/
theorem eq_of_unitriangular_of_eq_lower_mul {S : Type} [inst : CommRing S] {n : ℕ}
    (A A' L : Matrix (Fin n) (Fin n) S)
    (hA : ∀ (i j : Fin n), j < i → A i j = (0 : S)) (hA1 : ∀ (i : Fin n), A i i = (1 : S))
    (hA' : ∀ (i j : Fin n), j < i → A' i j = (0 : S)) (hA'1 : ∀ (i : Fin n), A' i i = (1 : S))
    (hL : ∀ (i j : Fin n), i < j → L i j = (0 : S)) (h : A' = L * A) : A' = A := by
  classical
  have hAb : A.BlockTriangular id := fun i j hji => hA i j hji
  have hA'b : A'.BlockTriangular id := fun i j hji => hA' i j hji
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hAb]
    simp [hA1]
  have hu : IsUnit A.det := by rw [hdet]; exact isUnit_one
  have hLeq : L = A' * A⁻¹ := by
    rw [h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have : Invertible A := A.invertibleOfIsUnitDet hu
  have hLb : L.BlockTriangular id := hLeq ▸ hA'b.mul (Matrix.blockTriangular_inv_of_blockTriangular hAb)
  have hoff : ∀ i j, i ≠ j → L i j = 0 := fun i j hij =>
    (lt_or_gt_of_ne hij).elim (hL i j) fun hji => hLb hji
  have hdiag : ∀ i, L i i = 1 := by
    intro i
    have hii := congrFun (congrFun h i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hki => by rw [hoff i k (Ne.symm hki), zero_mul])
      (by simp), hA1, mul_one, hA'1] at hii
    exact hii.symm
  have hL1 : L = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hdiag]
    · simp [hoff i j hij, Matrix.one_apply_ne hij]
  rw [h, hL1, Matrix.one_mul]

end GlobalTheory.UnitriangularLowerMulEq

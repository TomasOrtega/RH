import Mathlib

namespace YgbHelp

/- English proof (translation)
Rewrite using `[← Matrix.det_transpose, Matrix.det_apply']`. Both sides reduce to the same expression.
-/
private lemma detT {R : Type} [CommRing R] {r : ℕ} (M : Matrix (Fin r) (Fin r) R) :
    M.det = ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : R) * ∏ i, M i (σ i) := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  rfl

end YgbHelp

/- English proof (translation)
Introduce `R inst r n B C`. Rewrite using `[YgbHelp.detT]`. Repeatedly rewrite using `[YgbHelp.detT, Matrix.mul_apply, Fintype.prod_sum, Finset.mul_sum, Matrix.submatrix_apply, id]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Reformulated.B.Ygb2.main :
    ∀ {R : Type} [inst : CommRing R] {r n : ℕ} (B : Matrix (Fin r) (Fin n) R) (C : Matrix (Fin n) (Fin r) R),
      (B * C).det = ∑ f : Fin r → Fin n, (∏ i : Fin r, B i (f i)) * (C.submatrix f id).det := by
  intro R inst r n B C
  rw [YgbHelp.detT]
  simp_rw [YgbHelp.detT, Matrix.mul_apply, Fintype.prod_sum, Finset.mul_sum, Matrix.submatrix_apply, id]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

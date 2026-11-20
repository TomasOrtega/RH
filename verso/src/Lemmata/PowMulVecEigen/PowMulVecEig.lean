import Mathlib

open MvPowerSeries

namespace Bl.PowMulVecEigen

variable {C : Type} [Field C]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.
-/
private lemma pow_mulVec_eig {n : ℕ} (A : Matrix (Fin n) (Fin n) C) (w : Fin n → C) (lam : C)
    (h : Matrix.mulVec A w = lam • w) (k : ℕ) :
    Matrix.mulVec (A ^ k) w = lam ^ k • w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, smul_smul, pow_succ]

/- English proof (translation)
Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities.
-/
theorem goal1 {n : ℕ} (A : Matrix (Fin n) (Fin n) C) (w : Fin n → C) (lam : C)
    (h : Matrix.mulVec A w = lam • w) (f : Polynomial C) :
    Matrix.mulVec (Polynomial.aeval A f) w = f.eval lam • w := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, Matrix.add_mulVec, hp, hq, Polynomial.eval_add, add_smul]
  | monomial k a =>
    rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      Matrix.smul_mulVec, pow_mulVec_eig A w lam h k, Polynomial.eval_monomial, smul_smul]

end Bl.PowMulVecEigen

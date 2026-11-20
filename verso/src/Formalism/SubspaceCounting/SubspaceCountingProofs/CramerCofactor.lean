import Formalism.SubspaceCounting.StatementW

namespace Formalism.G0

open Matrix in
/- English proof (translation)
Introduce `R _ r T σ a`. Establish `h : T.adjugate *ᵥ (T *ᵥ σ) = T.det • σ`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]`. Establish `h2` using `congrFun h a`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h2`.

Rewrite using `[mul_comm, ← h2]`. Conclude with `Finset.sum_congr rfl fun l _ => mul_comm _ _`.
-/
theorem cramer_cofactor : CramerCofactor := by
  intro R _ r T σ a
  have h : T.adjugate *ᵥ (T *ᵥ σ) = T.det • σ := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h2 := congrFun h a
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h2
  rw [mul_comm, ← h2]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

end Formalism.G0

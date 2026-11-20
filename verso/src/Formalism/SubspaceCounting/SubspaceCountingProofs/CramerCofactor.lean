import Formalism.SubspaceCounting.StatementW

namespace Formalism.G0

open Matrix in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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

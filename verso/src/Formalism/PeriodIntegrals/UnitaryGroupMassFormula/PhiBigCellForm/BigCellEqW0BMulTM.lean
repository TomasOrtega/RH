import Mathlib
import Formalism.PeriodIntegrals.LongWeylElementSquare

noncomputable section

open Matrix

namespace PI.SwBig.PhiFormProof

open PI.SwBig

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem bigCell_eq_w0B_mul_tM (k r : ℕ) (c : Fin r → ℂ) :
    bigCell k r c 1 = w0B k r * tM k r c := by
  ext i j
  simp only [w0B, tM, Matrix.mul_diagonal, bigCell, tv]
  split_ifs <;> simp_all

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exp_neg_eq_inv (k r : ℕ) (X : Mat k r) :
    NormedSpace.exp (-X) = (NormedSpace.exp X)⁻¹ :=
  Matrix.exp_neg X

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem phiForm : PhiForm := by
  intro k r X x Z X'
  rw [Phi, exp_neg_eq_inv, bigCell_eq_w0B_mul_tM]
  simp only [Matrix.mul_assoc]

end PI.SwBig.PhiFormProof

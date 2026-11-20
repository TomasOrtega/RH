import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AltCoeff
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Comb Equiv

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem CombDetDescFactorial.proof : CombDetDescFactorial.Statement := by
  intro m l
  rw [vandermondeOf_eq_det]

  set v : Fin m → ℚ := fun i => (l i : ℚ)
  have hA : (Matrix.of fun i j : Fin m => ((l i).descFactorial (stair m j) : ℚ)) =
      (Matrix.of fun i j : Fin m => (descPochhammer ℚ (j : ℕ)).eval (v i)).submatrix
        id Fin.revPerm := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, id, Fin.revPerm_apply, v,
      descPochhammer_eval_eq_descFactorial, stair]
    rw [Fin.val_rev]
    congr 2
    omega
  have hB : (Matrix.of fun i j : Fin m => v i ^ (m - 1 - (j : ℕ))) =
      (Matrix.vandermonde v).submatrix id Fin.revPerm := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, id, Fin.revPerm_apply, Fin.val_rev,
      Matrix.vandermonde_apply]
    congr 1
    omega
  rw [hA, hB, Matrix.det_permute', Matrix.det_permute',
    Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde v
      (fun j => descPochhammer ℚ (j : ℕ))
      (fun j => descPochhammer_natDegree ℚ _)
      (fun j => monic_descPochhammer ℚ _)]

end GroundTheory.Heights₂.Heights.RestTerms

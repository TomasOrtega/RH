import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CoreStar

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def djVarMat (k j ρ : ℕ) :
    Matrix (Fin j) (Fin j)
      (MvPolynomial ((Fin (2 * (j + ρ) + k + 1) × Fin (2 * (j + ρ) + k + 1)) ⊕
        (Fin (2 * (j + ρ) + k + 1) × Fin (2 * (j + ρ) + k + 1))) ℂ) :=
  fun a b => MvPolynomial.X (Sum.inl (⟨2 * (j + ρ) + k - a.val, by omega⟩, ⟨b.val, by omega⟩))

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem isPolyDeg_determinant_derivative (k j ρ : ℕ) : IsPolyDeg j (DjU k j ρ) := by
  refine ⟨∑ σ : Equiv.Perm (Fin j),
      MvPolynomial.C ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) * ∏ i, djVarMat k j ρ (σ i) i, ?_, ?_⟩
  · refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
    refine Finset.sup_le fun σ _ => ?_
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    calc (∑ i : Fin j, (djVarMat k j ρ (σ i) i).totalDegree) ≤ ∑ _i : Fin j, 1 := by
          refine Finset.sum_le_sum fun i _ => ?_
          simp [djVarMat, MvPolynomial.totalDegree_X]
      _ = j := by simp
  · intro g
    rw [DjU, Matrix.det_apply']
    simp only [map_sum, map_mul, map_prod, MvPolynomial.eval_C]
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [djVarMat, Zh, MvPolynomial.eval_X]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem determinant_derivative_polynomial : DjPoly := fun k j ρ => isPolyDeg_determinant_derivative k j ρ

end PI.UnitaryCorollaryDerivatives

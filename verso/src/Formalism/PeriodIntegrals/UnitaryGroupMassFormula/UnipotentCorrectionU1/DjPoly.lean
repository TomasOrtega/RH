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
Use `⟨∑ σ : Equiv.Perm (Fin j), MvPolynomial.C ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) * ∏ i, djVarMat k j ρ (σ i) i, ?_, ?_⟩` and prove the remaining obligations. Use `(MvPolynomial.totalDegree_finsetSum _ _).trans ?_` and prove the remaining obligations. Use `Finset.sup_le fun σ _ => ?_` and prove the remaining obligations. Use `(MvPolynomial.totalDegree_mul _ _).trans ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.totalDegree_C, zero_add]`.

Use `(MvPolynomial.totalDegree_finsetProd _ _).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Simplify using `[djVarMat, MvPolynomial.totalDegree_X]`. Use `_ = j := by simp`.

Introduce `g`. Rewrite using `[DjU, Matrix.det_apply']`. Simplify using `only [map_sum, map_mul, map_prod, MvPolynomial.eval_C]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Use `congr 1`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[djVarMat, Zh, MvPolynomial.eval_X]`.
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
Introduce `k j ρ` and use `isPolyDeg_determinant_derivative k j ρ`.
-/
theorem determinant_derivative_polynomial : DjPoly := fun k j ρ => isPolyDeg_determinant_derivative k j ρ

end PI.UnitaryCorollaryDerivatives

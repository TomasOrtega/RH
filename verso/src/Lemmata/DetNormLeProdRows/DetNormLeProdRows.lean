import Mathlib
import Formalism.GelfandTransference.Statement

namespace Bl.DetNormLeProdRows

/- English proof (translation)
Set `v : Fin ρ → EuclideanSpace ℂ (Fin ρ)` to `fun i => WithLp.toLp 2 (A i)`. Establish `h : Module.finrank ℂ (EuclideanSpace ℂ (Fin ρ)) = Fintype.card (Fin ρ)` using `by simp`. Set `e` to `(EuclideanSpace.basisFun (Fin ρ) ℂ).toBasis`. Set `b` to `InnerProductSpace.gramSchmidtOrthonormalBasis h v`. Establish `he : e.det v = A.det`.

Rewrite using `[Module.Basis.det_apply, ← Matrix.det_transpose A]`. Use `congr 1`. Establish `hbv : b.toBasis.det v = b.toBasis.det e * e.det v`. Rewrite using `[Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply, ← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix]`. Establish `hb1 : ‖b.toBasis.det e‖ = 1`.

Simplify using `[e]`. Establish `key : ‖A.det‖ = ‖b.toBasis.det v‖`. Rewrite using `[hbv, norm_mul, hb1, one_mul, he]`. Rewrite using `[key, InnerProductSpace.gramSchmidtOrthonormalBasis_det h v, norm_prod]`. Apply `Finset.prod_le_prod (fun i _ => norm_nonneg _)` to reduce the goal to its premises.

Introduce `i _`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem det_norm_le_prod_rows (ρ : ℕ) (A : Matrix (Fin ρ) (Fin ρ) ℂ) :
    ‖A.det‖ ≤ ∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℂ (Fin ρ))‖ := by
  classical
  let v : Fin ρ → EuclideanSpace ℂ (Fin ρ) := fun i => WithLp.toLp 2 (A i)
  have h : Module.finrank ℂ (EuclideanSpace ℂ (Fin ρ)) = Fintype.card (Fin ρ) := by simp
  let e := (EuclideanSpace.basisFun (Fin ρ) ℂ).toBasis
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis h v
  have he : e.det v = A.det := by
    rw [Module.Basis.det_apply, ← Matrix.det_transpose A]
    congr 1
  have hbv : b.toBasis.det v = b.toBasis.det e * e.det v := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply, ← Matrix.det_mul,
      Module.Basis.toMatrix_mul_toMatrix]
  have hb1 : ‖b.toBasis.det e‖ = 1 := by
    simp [e]
  have key : ‖A.det‖ = ‖b.toBasis.det v‖ := by
    rw [hbv, norm_mul, hb1, one_mul, he]
  rw [key, InnerProductSpace.gramSchmidtOrthonormalBasis_det h v, norm_prod]
  apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
  intro i _
  calc ‖inner ℂ (b i) (v i)‖ ≤ ‖b i‖ * ‖v i‖ := norm_inner_le_norm _ _
    _ = ‖v i‖ := by rw [b.orthonormal.1 i, one_mul]

/- English proof (translation)
Introduce `ρ A`. Establish `h0` using `det_norm_le_prod_rows ρ A`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.prod_pow]`. Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations.

Rewrite using `[EuclideanSpace.norm_sq_eq]`.
-/
theorem goal1 :
  Formalism.HadamardInequality.Hadamard := by
  intro ρ A
  have h0 := det_norm_le_prod_rows ρ A
  calc ‖A.det‖ ^ 2 ≤ (∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℂ (Fin ρ))‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h0 2
    _ = ∏ i, ∑ j, ‖A i j‖ ^ 2 := by
        rw [← Finset.prod_pow]
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [EuclideanSpace.norm_sq_eq]

end Bl.DetNormLeProdRows

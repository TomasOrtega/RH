import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFrameJacobianSum
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCauchyBinet
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Finset Module

noncomputable section

namespace FrameJacobianSumAlt

variable {d : ℕ} {ι : Type*} [Fintype ι]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem real_inner_eq_re (x y : EuclideanSpace ℂ ι) : inner ℝ x y = (inner ℂ x y).re := by
  simp [PiLp.inner_apply, Complex.re_sum, Complex.inner]

/- English proof (translation)
Use symmetry to reverse the relation. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem adjoint_restrictScalars (S : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ ι) :
    LinearMap.adjoint (S.restrictScalars ℝ) = (LinearMap.adjoint S).restrictScalars ℝ := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, real_inner_eq_re,
    real_inner_eq_re, LinearMap.adjoint_inner_left]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem areaJacobian_restrictScalars (S : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ ι) :
    areaJacobian (S.restrictScalars ℝ) = ‖LinearMap.det (LinearMap.adjoint S ∘ₗ S)‖ := by
  rw [areaJacobian, adjoint_restrictScalars, ← LinearMap.restrictScalars_comp,
    LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.norm_def]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.
-/
theorem det_adjoint_comp (S : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ ι) :
    LinearMap.det (LinearMap.adjoint S ∘ₗ S) =
      (Matrix.of fun i j : Fin d => inner ℂ (S (EuclideanSpace.basisFun (Fin d) ℂ i))
        (S (EuclideanSpace.basisFun (Fin d) ℂ j))).det := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin d) ℂ).toBasis]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, LinearMap.comp_apply,
    LinearMap.adjoint_inner_right, Matrix.of_apply]

end FrameJacobianSumAlt

open FrameJacobianSumAlt in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem FrameJacobianSum.proof : FrameJacobianSum.Statement := by
  intro d n T b
  classical
  set e := EuclideanSpace.basisFun (Fin d) ℂ
  set N : Matrix (Fin n) (Fin d) ℂ := Matrix.of fun k j => inner ℂ (b k) (T (e j)) with hN
  have hI : ∀ (I : Finset (Fin n)) (h : I.card = d),
      areaJacobian ((frameProjLin b I ∘ₗ T).restrictScalars ℝ) = ‖(rowsOf N ⟨I, h⟩).det‖ ^ 2 := by
    intro I h
    rw [areaJacobian_restrictScalars, det_adjoint_comp]
    have hG : (Matrix.of fun i j : Fin d => inner ℂ ((frameProjLin b I ∘ₗ T) (e i))
        ((frameProjLin b I ∘ₗ T) (e j))) = (rowsOf N ⟨I, h⟩)ᴴ * rowsOf N ⟨I, h⟩ := by
      ext i j
      rw [Matrix.of_apply, PiLp.inner_apply, mul_apply, ← (I.orderIsoOfFin h).toEquiv.sum_comp]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp [rowsOf, hN, frameProjLin, conjTranspose_apply, e, RCLike.inner_apply, mul_comm]
    rw [hG, det_mul, det_conjTranspose, Complex.star_def, Complex.conj_mul', norm_pow,
      Complex.norm_real, norm_norm]
  have hT : LinearMap.det (LinearMap.adjoint T ∘ₗ T) =
      ∑ I : {I : Finset (Fin n) // I.card = d}, ((‖(rowsOf N I).det‖ ^ 2 : ℝ) : ℂ) := by
    rw [det_adjoint_comp]
    have hG : (Matrix.of fun i j : Fin d => inner ℂ (T (e i)) (T (e j))) = Nᴴ * N := by
      ext i j
      rw [Matrix.of_apply, ← b.sum_inner_mul_inner, mul_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [hN, conjTranspose_apply]
    rw [hG, CauchyBinet.proof]
    refine Finset.sum_congr rfl fun I _ => ?_
    have hc : colsOf Nᴴ I = (rowsOf N I)ᴴ := by
      ext i j
      simp [colsOf, rowsOf, conjTranspose_apply]
    rw [hc, det_conjTranspose, Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  rw [areaJacobian_restrictScalars, hT, ← Complex.ofReal_sum, Complex.norm_real,
    Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity),
    Finset.sum_subtype (univ.powersetCard d) (p := fun I : Finset (Fin n) => I.card = d)
      (fun I => by simp [mem_powersetCard])]
  exact Finset.sum_congr rfl fun I _ => (hI I.1 I.2).symm

end

end GroundTheory.Heights₂.Heights

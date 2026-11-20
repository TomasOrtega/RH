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
Simplify using `[PiLp.inner_apply, Complex.re_sum, Complex.inner]`.
-/
theorem real_inner_eq_re (x y : EuclideanSpace ℂ ι) : inner ℝ x y = (inner ℂ x y).re := by
  simp [PiLp.inner_apply, Complex.re_sum, Complex.inner]

/- English proof (translation)
Use `symm`. Rewrite using `[LinearMap.eq_adjoint_iff]`. Introduce `x y`. Rewrite using `[LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, real_inner_eq_re, real_inner_eq_re, LinearMap.adjoint_inner_left]`.
-/
theorem adjoint_restrictScalars (S : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ ι) :
    LinearMap.adjoint (S.restrictScalars ℝ) = (LinearMap.adjoint S).restrictScalars ℝ := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, real_inner_eq_re,
    real_inner_eq_re, LinearMap.adjoint_inner_left]

/- English proof (translation)
Rewrite using `[areaJacobian, adjoint_restrictScalars, ← LinearMap.restrictScalars_comp, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.norm_def]`.
-/
theorem areaJacobian_restrictScalars (S : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ ι) :
    areaJacobian (S.restrictScalars ℝ) = ‖LinearMap.det (LinearMap.adjoint S ∘ₗ S)‖ := by
  rw [areaJacobian, adjoint_restrictScalars, ← LinearMap.restrictScalars_comp,
    LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.norm_def]

/- English proof (translation)
Rewrite using `[← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin d) ℂ).toBasis]`. Use `congr 1`. Use extensionality with `i j`. Rewrite using `[LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, LinearMap.adjoint_inner_right, Matrix.of_apply]`.
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
Introduce `d n T b`. Use `set e := EuclideanSpace.basisFun (Fin d) ℂ`. Use `set N : Matrix (Fin n) (Fin d) ℂ := Matrix.of fun k j => inner ℂ (b k) (T (e j)) with hN`. Establish `hI : ∀ (I : Finset (Fin n)) (h : I.card = d), areaJacobian ((frameProjLin b I ∘ₗ T).restrictScalars ℝ) = ‖(rowsOf N ⟨I, h⟩).det‖ ^ 2`. Introduce `I h`.

Rewrite using `[areaJacobian_restrictScalars, det_adjoint_comp]`. Establish `hG : (Matrix.of fun i j : Fin d => inner ℂ ((frameProjLin b I ∘ₗ T) (e i)) ((frameProjLin b I ∘ₗ T) (e j))) = (rowsOf N ⟨I, h⟩)ᴴ * rowsOf N ⟨I, h⟩`. Use extensionality with `i j`. Rewrite using `[Matrix.of_apply, PiLp.inner_apply, mul_apply, ← (I.orderIsoOfFin h).toEquiv.sum_comp]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Simplify using `[rowsOf, hN, frameProjLin, conjTranspose_apply, e, RCLike.inner_apply, mul_comm]`. Rewrite using `[hG, det_mul, det_conjTranspose, Complex.star_def, Complex.conj_mul', norm_pow, Complex.norm_real, norm_norm]`. Establish `hT : LinearMap.det (LinearMap.adjoint T ∘ₗ T) = ∑ I : {I : Finset (Fin n) // I.card = d}, ((‖(rowsOf N I).det‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[det_adjoint_comp]`. Establish `hG : (Matrix.of fun i j : Fin d => inner ℂ (T (e i)) (T (e j))) = Nᴴ * N`.

Use extensionality with `i j`. Rewrite using `[Matrix.of_apply, ← b.sum_inner_mul_inner, mul_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `[hN, conjTranspose_apply]`. Rewrite using `[hG, CauchyBinet.proof]`.

Use `Finset.sum_congr rfl fun I _ => ?_` and prove the remaining obligations. Establish `hc : colsOf Nᴴ I = (rowsOf N I)ᴴ`. Use extensionality with `i j`. Simplify using `[colsOf, rowsOf, conjTranspose_apply]`. Rewrite using `[hc, det_conjTranspose, Complex.star_def, Complex.conj_mul']`.

Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[areaJacobian_restrictScalars, hT, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity), Finset.sum_subtype (univ.powersetCard d) (p := fun I : Finset (Fin n) => I.card = d) (fun I => by simp [mem_powersetCard])]`. Conclude with `Finset.sum_congr rfl fun I _ => (hI I.1 I.2).symm`.
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

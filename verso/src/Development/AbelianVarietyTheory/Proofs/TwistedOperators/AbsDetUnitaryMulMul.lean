import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

open Kronecker in

/- English proof (translation)
Introduce `p q U hU V hV T hT`. Set `e : (Fin p → Fin q → ℂ) ≃ₗ[ℂ] (Fin q → Fin p → ℂ)` to `{ toFun := fun B j i => B i j invFun := fun C i j => C j i map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl left_inv := fun _ => rfl right_inv := fun _ => rfl }`. Set `L : (Fin q → Fin p → ℂ) →ₗ[ℂ] (Fin q → Fin p → ℂ)` to `LinearMap.pi (fun j => (Matrix.toLin' U).comp (LinearMap.proj j))`. Set `R : (Fin p → Fin q → ℂ) →ₗ[ℂ] (Fin p → Fin q → ℂ)` to `LinearMap.pi (fun i => (Matrix.toLin' Vᵀ).comp (LinearMap.proj i))`. Set `C : (Fin p → Fin q → ℂ) →ₗ[ℂ] (Fin p → Fin q → ℂ)` to `((e.symm : (Fin q → Fin p → ℂ) →ₗ[ℂ] (Fin p → Fin q → ℂ)) ∘ₗ L ∘ₗ (e.symm.symm : (Fin p → Fin q → ℂ) →ₗ[ℂ] (Fin q → Fin p → ℂ))) ∘ₗ R`.

Establish `hTC : T = C.restrictScalars ℝ`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `B`. Use function extensionality and compare the values at `i j`. Establish `h` using `congrFun (congrFun (hT B) i) j`.

Simplify using `only [Matrix.of_apply] at h`. Rewrite using `[h, Matrix.mul_assoc]`. Simplify using `[C, L, R, e, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]`. Establish `hL : LinearMap.det L = U.det ^ q`. Simplify using `[L, LinearMap.det_pi, LinearMap.det_toLin']`.

Establish `hR : LinearMap.det R = V.det ^ p`. Simplify using `[R, LinearMap.det_pi, LinearMap.det_toLin', Matrix.det_transpose]`. Establish `hC : LinearMap.det C = U.det ^ q * V.det ^ p`. Simplify using `only [C]`. Rewrite using `[LinearMap.det_comp, LinearMap.det_conj L e.symm, hL, hR]`.

Establish `hu : ‖U.det‖ = 1` using `CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hU)`. Establish `hv : ‖V.det‖ = 1` using `CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hV)`. Rewrite using `[hTC, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, hC, map_mul, map_pow, map_pow, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hu, hv]`. Simplify using the standard rewrite rules.
-/
theorem abs_det_unitary_mul_mul : ∀ (p q : ℕ), ∀ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∀ V ∈ Matrix.unitaryGroup (Fin q) ℂ, ∀ T : (Fin p → Fin q → ℂ) →ₗ[ℝ] (Fin p → Fin q → ℂ), (∀ B, Matrix.of (T B) = U * Matrix.of B * V) → |LinearMap.det T| = 1 := by
  classical
  intro p q U hU V hV T hT

  let e : (Fin p → Fin q → ℂ) ≃ₗ[ℂ] (Fin q → Fin p → ℂ) :=
    { toFun := fun B j i => B i j
      invFun := fun C i j => C j i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

  let L : (Fin q → Fin p → ℂ) →ₗ[ℂ] (Fin q → Fin p → ℂ) :=
    LinearMap.pi (fun j => (Matrix.toLin' U).comp (LinearMap.proj j))

  let R : (Fin p → Fin q → ℂ) →ₗ[ℂ] (Fin p → Fin q → ℂ) :=
    LinearMap.pi (fun i => (Matrix.toLin' Vᵀ).comp (LinearMap.proj i))
  let C : (Fin p → Fin q → ℂ) →ₗ[ℂ] (Fin p → Fin q → ℂ) :=
    ((e.symm : (Fin q → Fin p → ℂ) →ₗ[ℂ] (Fin p → Fin q → ℂ)) ∘ₗ L ∘ₗ
      (e.symm.symm : (Fin p → Fin q → ℂ) →ₗ[ℂ] (Fin q → Fin p → ℂ))) ∘ₗ R
  have hTC : T = C.restrictScalars ℝ := by
    apply LinearMap.ext
    intro B
    funext i j
    have h := congrFun (congrFun (hT B) i) j
    simp only [Matrix.of_apply] at h
    rw [h, Matrix.mul_assoc]
    simp [C, L, R, e, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
  have hL : LinearMap.det L = U.det ^ q := by
    simp [L, LinearMap.det_pi, LinearMap.det_toLin']
  have hR : LinearMap.det R = V.det ^ p := by
    simp [R, LinearMap.det_pi, LinearMap.det_toLin', Matrix.det_transpose]
  have hC : LinearMap.det C = U.det ^ q * V.det ^ p := by
    simp only [C]
    rw [LinearMap.det_comp, LinearMap.det_conj L e.symm, hL, hR]
  have hu : ‖U.det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hU)
  have hv : ‖V.det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hV)
  rw [hTC, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, hC, map_mul, map_pow,
    map_pow, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hu, hv]
  simp

end GlobalTheory.PolarU

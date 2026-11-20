import Mathlib

/- English proof (translation)
Introduce `V _ _ _ B hB f hf`. Set `b` to `Module.finBasis ℝ V`. Establish `hcomp : B.comp f f = B`. Use extensionality with `x y`. Simplify using `using hf x y`.

Establish `hmat` using `LinearMap.BilinForm.toMatrix_comp b b B f f`. Rewrite `hmat` using `[hcomp]`. Establish `hne : (LinearMap.BilinForm.toMatrix b B).det ≠ 0` using `(LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB`. Establish `hdet` using `congrArg Matrix.det hmat`. Rewrite `hdet` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix]`.

Apply `mul_left_cancel₀ hne` to reduce the goal to its premises. Take the linear combination `-hdet`.
-/
theorem UpperTheory.Reformulated.B.Qm9.det_sq_eq_one_of_preserves_bilin.{u_1} :
    ∀ {V : Type u_1} [inst : AddCommGroup V]
    [inst_1 : _root_.Module ℝ V] [FiniteDimensional ℝ V] (B : LinearMap.BilinForm ℝ V),
    B.Nondegenerate →
      ∀ (f : V →ₗ[ℝ] V),
        (∀ (x y : V), ((B : V → V →ₗ[ℝ] ℝ) ((f : V → V) x) : V → ℝ) ((f : V → V) y) = ((B : V → V →ₗ[ℝ] ℝ) x : V → ℝ) y) →
          (LinearMap.det : (V →ₗ[ℝ] V) → ℝ) f ^ (2 : ℕ) = (1 : ℝ) := by
  intro V _ _ _ B hB f hf
  classical
  let b := Module.finBasis ℝ V
  have hcomp : B.comp f f = B := by
    ext x y
    simpa using hf x y
  have hmat := LinearMap.BilinForm.toMatrix_comp b b B f f
  rw [hcomp] at hmat
  have hne : (LinearMap.BilinForm.toMatrix b B).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix] at hdet
  apply mul_left_cancel₀ hne
  linear_combination -hdet

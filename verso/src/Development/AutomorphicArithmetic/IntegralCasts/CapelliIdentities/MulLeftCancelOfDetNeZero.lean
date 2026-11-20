import Mathlib

/- English proof (translation)
Introduce `R _ _ n A X Y hA h`. Establish `h2 : A.det • X = A.det • Y`. Establish `h3 : A.adjugate * (A * X) = A.adjugate * (A * Y)` using `by rw [h]`. Rewrite `h3` using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.one_mul]`. Conclude with `h3`.

Use extensionality with `i j`. Establish `h4 : A.det * X i j = A.det * Y i j` using `congrFun (congrFun h2 i) j`. Conclude with `mul_left_cancel₀ hA h4`.
-/
theorem UpperTheory.Reformulated.B.Yoa2.mul_left_cancel_of_det_ne_zero.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] [IsDomain R] {n : ℕ} {A X Y : Matrix (Fin n) (Fin n) R},
      A.det ≠ (0 : R) → A * X = A * Y → X = Y := by
  intro R _ _ n A X Y hA h
  have h2 : A.det • X = A.det • Y := by
    have h3 : A.adjugate * (A * X) = A.adjugate * (A * Y) := by rw [h]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.one_mul, Matrix.one_mul] at h3
    exact h3
  ext i j
  have h4 : A.det * X i j = A.det * Y i j := congrFun (congrFun h2 i) j
  exact mul_left_cancel₀ hA h4

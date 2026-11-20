import Mathlib

/- English proof (translation)
Introduce `n`. Establish `hc : Continuous (fun x : Fin n → Fin n → ℂ => (Matrix.of x : Matrix (Fin n) (Fin n) ℂ))` using `continuous_id`. Establish `hdet : Measurable (fun x : Fin n → Fin n → ℂ => (Matrix.of x : Matrix (Fin n) (Fin n) ℂ).det)` using `hc.matrix_det.measurable`. Use `measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_` and prove the remaining obligations. Establish `hadj : Measurable (fun x : Fin n → Fin n → ℂ => (Matrix.of x : Matrix (Fin n) (Fin n) ℂ).adjugate i j)` using `(hc.matrix_adjugate.matrix_elem i j).measurable`.

Establish `h` using `hdet.inv.mul hadj`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Simplify using `only [Matrix.of_symm_apply, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.inv_apply]`.
-/
theorem UpperTheory.measurable_matrix_inv :
    ∀ n : ℕ, Measurable (fun x : Fin n → Fin n → ℂ => (Matrix.of.symm ((Matrix.of x : Matrix (Fin n) (Fin n) ℂ)⁻¹) : Fin n → Fin n → ℂ)) := by
  intro n
  have hc : Continuous (fun x : Fin n → Fin n → ℂ => (Matrix.of x : Matrix (Fin n) (Fin n) ℂ)) :=
    continuous_id
  have hdet : Measurable (fun x : Fin n → Fin n → ℂ =>
      (Matrix.of x : Matrix (Fin n) (Fin n) ℂ).det) := hc.matrix_det.measurable
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  have hadj : Measurable (fun x : Fin n → Fin n → ℂ =>
      (Matrix.of x : Matrix (Fin n) (Fin n) ℂ).adjugate i j) :=
    (hc.matrix_adjugate.matrix_elem i j).measurable
  have h := hdet.inv.mul hadj
  convert h using 1
  funext x
  simp only [Matrix.of_symm_apply, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply,
    smul_eq_mul, Pi.mul_apply, Pi.inv_apply]

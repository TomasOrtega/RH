import Mathlib
open scoped Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ n C`. Take `⟨L, L', d, hd⟩` from `Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal C`. Use `⟨Matrix.diagonal (fun i => if d i = 0 then 1 else (d i)⁻¹) * (L.map Matrix.TransvectionStruct.toMatrix).prod, (L'.map Matrix.TransvectionStruct.toMatrix).prod, fun i => if d i = 0 then 0 else 1, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_mul, Matrix.TransvectionStruct.det_toMatrix_prod, mul_one, Matrix.det_diagonal]`. Use `Finset.prod_ne_zero_iff.mpr fun i _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `by_cases h : d i = 0 <;> simp [h]`. Rewrite using `[Matrix.TransvectionStruct.det_toMatrix_prod]`. Conclude with `one_ne_zero`. Apply the tactic sequence `intro i; by_cases h : d i = 0 <;> simp [h]`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ C, hd, Matrix.diagonal_mul_diagonal]`.

Apply the tactic sequence `congr 1; funext i; by_cases h : d i = 0 <;> simp [h]`.
-/
theorem rank_normal_form_field : ∀ (k : Type) [Field k] (n : ℕ) (C : Matrix (Fin n) (Fin n) k),
    ∃ (U P : Matrix (Fin n) (Fin n) k) (e : Fin n → k), U.det ≠ 0 ∧ P.det ≠ 0 ∧ (∀ i, e i = 0 ∨ e i = 1) ∧
      U * C * P = Matrix.diagonal e := by
  intro k _ n C
  classical
  obtain ⟨L, L', d, hd⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal C
  refine ⟨Matrix.diagonal (fun i => if d i = 0 then 1 else (d i)⁻¹) * (L.map Matrix.TransvectionStruct.toMatrix).prod,
    (L'.map Matrix.TransvectionStruct.toMatrix).prod, fun i => if d i = 0 then 0 else 1, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.TransvectionStruct.det_toMatrix_prod, mul_one, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    by_cases h : d i = 0 <;> simp [h]
  · rw [Matrix.TransvectionStruct.det_toMatrix_prod]; exact one_ne_zero
  · intro i; by_cases h : d i = 0 <;> simp [h]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ C, hd, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; by_cases h : d i = 0 <;> simp [h]

end GlobalTheory

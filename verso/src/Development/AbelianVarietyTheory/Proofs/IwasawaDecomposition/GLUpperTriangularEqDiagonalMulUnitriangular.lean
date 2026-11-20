import Mathlib

open Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `n B hB`. Establish `hdet : B.val.det = ∏ i, B.val i i` using `Matrix.det_of_upperTriangular hB`. Establish `hdet0 : B.val.det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det _).mp B.isUnit).ne_zero`. Establish `hne : ∀ i, B.val i i ≠ 0`. Introduce `i h`.

Apply `hdet0` to reduce the goal to its premises. Rewrite using `[hdet]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) h`. Set `D : GL (Fin n) ℂ` to `⟨diagonal (fun i => B.val i i), diagonal (fun i => (B.val i i)⁻¹), by`. Rewrite using `[diagonal_mul_diagonal, ← diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `mul_inv_cancel₀ (hne i),`. Use `by`. Rewrite using `[diagonal_mul_diagonal, ← diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `inv_mul_cancel₀ (hne i)⟩`. Establish `hU : ∀ i j, (D⁻¹ * B).val i j = (B.val i i)⁻¹ * B.val i j`. Introduce `i j`.

Express the relevant statement in the definitionally equal form `(diagonal (fun i => (B.val i i)⁻¹) * B.val) i j = _`. Rewrite using `[diagonal_mul]`. Use `⟨D, D⁻¹ * B, by simp, isDiag_diagonal _, fun i => diagonal_apply_eq _ _, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Rewrite using `[hU, hB hij, mul_zero]`.

Introduce `i`. Rewrite using `[hU, inv_mul_cancel₀ (hne i)]`.
-/
theorem GL_upperTriangular_eq_diagonal_mul_unitriangular :
    ∀ (n : ℕ) (B : GL (Fin n) ℂ), B.val.BlockTriangular id → ∃ D U : GL (Fin n) ℂ,
      B = D * U ∧ D.val.IsDiag ∧ (∀ i, D.val i i = B.val i i) ∧
      U.val.BlockTriangular id ∧ ∀ i, U.val i i = 1 := by
  intro n B hB
  have hdet : B.val.det = ∏ i, B.val i i := Matrix.det_of_upperTriangular hB
  have hdet0 : B.val.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp B.isUnit).ne_zero
  have hne : ∀ i, B.val i i ≠ 0 := by
    intro i h
    apply hdet0
    rw [hdet]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h
  let D : GL (Fin n) ℂ :=
    ⟨diagonal (fun i => B.val i i), diagonal (fun i => (B.val i i)⁻¹),
      by
        rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i; exact mul_inv_cancel₀ (hne i),
      by
        rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i; exact inv_mul_cancel₀ (hne i)⟩
  have hU : ∀ i j, (D⁻¹ * B).val i j = (B.val i i)⁻¹ * B.val i j := by
    intro i j
    change (diagonal (fun i => (B.val i i)⁻¹) * B.val) i j = _
    rw [diagonal_mul]
  refine ⟨D, D⁻¹ * B, by simp, isDiag_diagonal _, fun i => diagonal_apply_eq _ _, ?_, ?_⟩
  · intro i j hij
    rw [hU, hB hij, mul_zero]
  · intro i
    rw [hU, inv_mul_cancel₀ (hne i)]

end GlobalTheory

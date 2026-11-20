import Mathlib

open Matrix Polynomial ComplexOrder

namespace Bl.general_b_fact_right_bis

/- English proof (translation)
Establish `hdet : (Matrix.scalar (Fin k) μ - G).det = 0`. Rewrite using `[← Matrix.eval_charpoly]`. Conclude with `hμ`. Take `⟨v, hv, h⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hdet`. Use `⟨v, hv, ?_⟩` and prove the remaining obligations.

Rewrite `h` using `[Matrix.sub_mulVec, sub_eq_zero]`. Rewrite using `[← h]`. Use extensionality with `i`. Simplify using `[Matrix.scalar_apply, Matrix.mulVec_diagonal]`.
-/
theorem goal1 {k : ℕ} (G : Matrix (Fin k) (Fin k) ℂ) (μ : ℂ) (hμ : G.charpoly.IsRoot μ) :
    ∃ v : Fin k → ℂ, v ≠ 0 ∧ G *ᵥ v = μ • v := by
  have hdet : (Matrix.scalar (Fin k) μ - G).det = 0 := by
    rw [← Matrix.eval_charpoly]; exact hμ
  obtain ⟨v, hv, h⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero] at h
  rw [← h]
  ext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

end Bl.general_b_fact_right_bis

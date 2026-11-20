import Mathlib
import Formalism.LocalToGlobal.AdelicCompactOpens.HermDefONFamily

namespace PI.UnitaryGroupMassFormula.HermDefON

open Matrix
open scoped ComplexOrder

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Both sides reduce to the same expression.
-/
private theorem exists_unitary_diagonal_pos_of_posDef {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (μ : Fin n → ℝ), Uᴴ * U = 1 ∧ (∀ i, 0 < μ i) ∧
      G = U * diagonal (fun i => (μ i : ℂ)) * Uᴴ := by
  refine ⟨(hG.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ), hG.1.eigenvalues, ?_,
    fun i => hG.eigenvalues_pos i, ?_⟩
  · have h := hG.1.eigenvectorUnitary.2
    rw [Matrix.mem_unitaryGroup_iff'] at h
    simpa [Matrix.star_eq_conjTranspose] using h
  · have h := hG.1.spectral_theorem
    refine h.trans ?_
    rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem exists_congr_one {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef) :
    ∃ y : Matrix (Fin n) (Fin n) ℂ, IsUnit y.det ∧ yᴴ * G * y = 1 := by
  classical
  obtain ⟨U, μ, hUU, hμ, hG'⟩ := exists_unitary_diagonal_pos_of_posDef G hG
  have hr : ∀ i, Real.sqrt (μ i) * (Real.sqrt (μ i))⁻¹ = 1 := fun i =>
    mul_inv_cancel₀ (Real.sqrt_pos.mpr (hμ i)).ne'
  have hr2 : ∀ i, (Real.sqrt (μ i))⁻¹ * μ i * (Real.sqrt (μ i))⁻¹ = 1 := by
    intro i
    have hs : Real.sqrt (μ i) ≠ 0 := (Real.sqrt_pos.mpr (hμ i)).ne'
    have hsq : Real.sqrt (μ i) * Real.sqrt (μ i) = μ i := Real.mul_self_sqrt (hμ i).le
    calc (Real.sqrt (μ i))⁻¹ * μ i * (Real.sqrt (μ i))⁻¹
        = (Real.sqrt (μ i))⁻¹ * (Real.sqrt (μ i) * Real.sqrt (μ i)) * (Real.sqrt (μ i))⁻¹ := by
          rw [hsq]
      _ = 1 := by rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul, mul_inv_cancel₀ hs]
  let d : Fin n → ℂ := fun i => (((Real.sqrt (μ i))⁻¹ : ℝ) : ℂ)
  let e : Fin n → ℂ := fun i => ((Real.sqrt (μ i) : ℝ) : ℂ)
  have hde : ∀ i, e i * d i = 1 := by
    intro i
    show ((Real.sqrt (μ i) : ℝ) : ℂ) * (((Real.sqrt (μ i))⁻¹ : ℝ) : ℂ) = 1
    rw [← Complex.ofReal_mul, hr i, Complex.ofReal_one]
  have hdd : ∀ i, d i * (μ i : ℂ) * d i = 1 := by
    intro i
    show (((Real.sqrt (μ i))⁻¹ : ℝ) : ℂ) * (μ i : ℂ) * (((Real.sqrt (μ i))⁻¹ : ℝ) : ℂ) = 1
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hr2 i, Complex.ofReal_one]
  have hdH : (diagonal d)ᴴ = diagonal d := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp [d]
  refine ⟨U * diagonal d, ?_, ?_⟩
  · have h : diagonal e * Uᴴ * (U * diagonal d) = 1 := by
      calc diagonal e * Uᴴ * (U * diagonal d) = diagonal e * (Uᴴ * U) * diagonal d := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by
          rw [hUU, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
          simp only [hde]
          exact Matrix.diagonal_one
    exact Matrix.isUnit_det_of_left_inverse h
  · rw [Matrix.conjTranspose_mul, hdH, hG']
    calc diagonal d * Uᴴ * (U * diagonal (fun i => (μ i : ℂ)) * Uᴴ) * (U * diagonal d)
        = diagonal d * (Uᴴ * U) * diagonal (fun i => (μ i : ℂ)) * (Uᴴ * U) * diagonal d := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hUU, Matrix.mul_one, Matrix.mul_one, Matrix.diagonal_mul_diagonal,
          Matrix.diagonal_mul_diagonal]
        simp only [hdd]
        exact Matrix.diagonal_one

end PI.UnitaryGroupMassFormula.HermDefON

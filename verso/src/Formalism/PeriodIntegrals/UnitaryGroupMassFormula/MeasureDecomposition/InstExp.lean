import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDefs

noncomputable section

open Matrix

namespace PI.ScMuExists.UnitaryGroupMassFormula

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem inst_exp_real_entry (l : ℝ) (y : ℂ) :
    NormedSpace.exp (l : ℂ) * y = y ↔ (l : ℂ) * y = 0 := by
  have hE : NormedSpace.exp (l : ℂ) = ((Real.exp l : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    first
      | rw [Complex.exp_eq_exp_ℂ]
      | exact (congrFun Complex.exp_eq_exp_ℂ (l : ℂ)).symm
  rw [hE]
  constructor
  · intro h
    by_cases hy : y = 0
    · simp [hy]
    · have h1 : ((Real.exp l : ℝ) : ℂ) = 1 := mul_right_cancel₀ hy (h.trans (one_mul y).symm)
      have h2 : Real.exp l = 1 := by exact_mod_cast h1
      have h3 : l = 0 := Real.exp_eq_one_iff l |>.mp h2
      simp [h3]
  · intro h
    rcases mul_eq_zero.mp h with hl | hy
    · have h3 : l = 0 := by exact_mod_cast hl
      simp [h3]
    · simp [hy]

/- English proof (translation)
Establish an intermediate fact. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Reduce the conclusion to the remaining proof obligations. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Simplify using the standard rewrite rules.

Treat this case separately. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem exists_unitary_diagonal_of_isHermitian {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), star U * U = 1 ∧ U * star U = 1 ∧
      X = U * diagonal (fun i => (d i : ℂ)) * star U := by
  have h1 : star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    first
      | exact hX.eigenvectorUnitary.2.1
      | exact (Matrix.mem_unitaryGroup_iff'.mp hX.eigenvectorUnitary.2)
      | exact Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2
      | exact unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2
  have h2 : (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    first
      | exact hX.eigenvectorUnitary.2.2
      | exact (Matrix.mem_unitaryGroup_iff.mp hX.eigenvectorUnitary.2)
      | exact Unitary.mul_star_self_of_mem hX.eigenvectorUnitary.2
      | exact unitary.mul_star_self_of_mem hX.eigenvectorUnitary.2
  refine ⟨hX.eigenvectorUnitary, hX.eigenvalues, h1, h2, ?_⟩
  first
    | (conv_lhs => rw [hX.spectral_theorem]); simp [Function.comp_def]
    | (conv_lhs => rw [hX.spectral_theorem]); simp [Function.comp_def, Unitary.conjStarAlgAut_apply]
    | (have h3 := hX.star_mul_self_mul_eq_diagonal
       calc X = (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
              (star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * X *
                (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) *
              star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by
             simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
             rw [Matrix.mul_assoc, h2, Matrix.mul_one]
         _ = _ := by rw [h3]; simp [Function.comp_def])

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exponent_fixed_instance : InstExpFix := by
  intro n X hX w
  obtain ⟨U, d, hUU, hUU', hX'⟩ := exists_unitary_diagonal_of_isHermitian X hX
  have hexp : NormedSpace.exp X = U * diagonal (fun i => NormedSpace.exp (d i : ℂ)) * star U := by
    have hunit : IsUnit U := ⟨⟨U, star U, hUU', hUU⟩, rfl⟩
    have hinv : U⁻¹ = star U := Matrix.inv_eq_left_inv hUU
    rw [hX', ← hinv]
    have hd : NormedSpace.exp (diagonal (fun i => (d i : ℂ))) =
        diagonal (fun i => NormedSpace.exp (d i : ℂ)) := by
      rw [Matrix.exp_diagonal]
      congr 1
      funext i
      first
        | exact Pi.exp_apply _ _
        | simp [Pi.exp_def]
        | rfl
    first
      | rw [Matrix.exp_conj _ _ hunit, hd]
      | rw [Matrix.exp_conj ℂ _ _ hunit, hd]
  have inj : ∀ a b : Fin n → ℂ, U *ᵥ a = U *ᵥ b → a = b := by
    intro a b h
    have h2 := congrArg (fun v => star U *ᵥ v) h
    simpa only [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec] using h2
  obtain ⟨y, hy⟩ : ∃ y, y = star U *ᵥ w := ⟨_, rfl⟩
  have hw : w = U *ᵥ y := by rw [hy, Matrix.mulVec_mulVec, hUU', Matrix.one_mulVec]
  have hXw : X *ᵥ w = U *ᵥ (fun i => (d i : ℂ) * y i) := by
    rw [hX', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hy]
    congr 1
    funext i
    rw [Matrix.mulVec_diagonal]
  have hEw : NormedSpace.exp X *ᵥ w = U *ᵥ (fun i => NormedSpace.exp (d i : ℂ) * y i) := by
    rw [hexp, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hy]
    congr 1
    funext i
    rw [Matrix.mulVec_diagonal]
  constructor
  · intro h
    have h1 : (fun i => NormedSpace.exp (d i : ℂ) * y i) = y := by
      apply inj
      rw [← hEw, h]
      exact hw
    rw [hXw]
    have h0 : (fun i => (d i : ℂ) * y i) = 0 := by
      funext i
      exact (inst_exp_real_entry (d i) (y i)).mp (congrFun h1 i)
    rw [h0, Matrix.mulVec_zero]
  · intro h
    rw [hXw] at h
    have h2 : (fun i => (d i : ℂ) * y i) = 0 := inj _ 0 (by rw [h, Matrix.mulVec_zero])
    rw [hEw]
    have h3 : (fun i => NormedSpace.exp (d i : ℂ) * y i) = y := by
      funext i
      exact (inst_exp_real_entry (d i) (y i)).mpr (congrFun h2 i)
    rw [h3, ← hw]

end PI.ScMuExists.UnitaryGroupMassFormula

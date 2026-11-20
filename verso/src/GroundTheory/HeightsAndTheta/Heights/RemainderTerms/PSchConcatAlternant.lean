import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem SchConcatAlternant.alternant_comp_perm {N : ℕ} (w : Fin N → ℕ) (τ : Equiv.Perm (Fin N)) :
    alternant (w ∘ τ) = C ((Equiv.Perm.sign τ : ℤ) : ℚ) * alternant w := by
  unfold alternant
  have hM : (Matrix.of fun i i' : Fin N =>
      (X i : MvPolynomial (Fin N) ℚ) ^ (w ∘ τ) i') =
      (Matrix.of fun i i' : Fin N => (X i : MvPolynomial (Fin N) ℚ) ^ w i').submatrix id τ := rfl
  rw [hM, Matrix.det_permute', map_intCast]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem SchConcatAlternant.alternant_add_staircase {N : ℕ} (mu : Fin N → ℕ) :
    alternant (fun p : Fin N => mu p + (N - 1 - (p : ℕ))) =
      vandermondeOf (fun p : Fin N => (X p : MvPolynomial (Fin N) ℚ)) * schur (Fin N) mu := by
  rw [mul_comm, ← Schur.det_pow_add_staircase_eq, ← Matrix.det_transpose]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities.
-/
theorem SchConcatAlternant.proof (h1 : SchAlternantRenamePlace.Statement)
    (h2 : SchConcatExponent.Statement) : SchConcatAlternant.Statement := by
  intro r a c
  obtain ⟨τ, hτ⟩ := h2 r a c
  refine ⟨((Equiv.Perm.sign τ : ℤ) : ℚ), ?_, fun lam hlam => ?_⟩
  · rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]
  · rw [h1, hτ lam hlam, SchConcatAlternant.alternant_comp_perm,
      SchConcatAlternant.alternant_add_staircase,
      Schur.schur_padPartition (Fin (r + a)) (fun i : Fin r => lam i - a) (r + a) (by omega), map_mul,
      rename_C]

end

end GroundTheory.Heights₂.Heights.RestTerms

import Mathlib
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory
open Matrix in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem eh_inv_entry : ∀ (k r : ℕ) (a b c i : Fin (2 * r + k + 1)), ∀ g ∈ B.GV k r, Q.EH k r a b (fun y : B.Mat k r => y⁻¹ c i) g = -(if a = c then g⁻¹ b i else 0) := by
  intro k r a b c i g _
  have h := Formalism.FourierDecayAlt.P.Qx5.eh_inv (k := k) (r := r) (LinearMap.proj c) (Pi.single i 1) g a b
  have e : (fun y : B.Mat k r => y⁻¹ c i) = fun y : B.Mat k r => (LinearMap.proj c : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ) (y⁻¹ *ᵥ Pi.single i 1) := by
    funext y
    simp [Matrix.mulVec_single_one]
  rw [e]
  refine h.trans ?_
  by_cases hac : a = c
  · subst hac
    simp [Matrix.mulVec, dotProduct, Matrix.single, Pi.single_apply]
  · simp [Matrix.mulVec, dotProduct, Matrix.single, hac]
end GlobalTheory

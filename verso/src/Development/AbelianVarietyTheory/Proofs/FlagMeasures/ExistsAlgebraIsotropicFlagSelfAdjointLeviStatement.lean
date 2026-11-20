import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAlgebraIsotropicFlagSelfAdjointLevi
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LeviAlgebra.exists_levi_algebra` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsAlgebraIsotropicFlagSelfAdjointLevi.lean&line=313#L313)
-/
theorem _root_.GlobalTheory.T.exists_algebra_isotropicFlagSelfAdjointLevi : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∃ (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) ∧ (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) ∧ flagM ε W = {g | uMat g - 1 ∈ A} := by
  first | exact @GlobalTheory.LeviAlgebra.exists_levi_algebra | exact GlobalTheory.LeviAlgebra.exists_levi_algebra | (intros; apply GlobalTheory.LeviAlgebra.exists_levi_algebra <;> assumption)

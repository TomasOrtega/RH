import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobianActionUpperRightBlockExpCoords
import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FJacobianActionUpperRightBlockExpCoords.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.jacobian_action_upperRightBlock_exp_coords : ∀ (p q : ℕ) (g : Mat p q) (ψ : (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ)), Continuous ψ → (∀ B, ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ, NormedSpace.exp (pY B) * g = Matrix.fromBlocks U 0 0 V * NormedSpace.exp (pY (ψ B))) → (∀ B : Fin p → Fin q → ℂ, 0 < LinearMap.det (sP (pY B))) → (∀ B C : Fin p → Fin q → ℂ, sAd (pY B) (pY C) = pY (sP (pY B) C)) → (∀ B : Fin p → Fin q → ℂ, ∃ A : (Fin p → Fin q → ℂ) →L[ℝ] (Ix p q → Ix p q → ℂ), HasStrictFDerivAt (fun (C : Fin p → Fin q → ℂ) (a b : Ix p q) => NormedSpace.exp (pY C + pY C) a b) A B ∧ ∀ C, Matrix.of (A C) = NormedSpace.exp (pY B) * sAd (pY B) (pY C + pY C) * NormedSpace.exp (pY B)) → ∀ B, ∃ P : (Fin p → Fin q → ℂ) →L[ℝ] (Fin p → Fin q → ℂ), HasFDerivAt ψ P B ∧ |P.det| * LinearMap.det (sP (pY (ψ B))) = LinearMap.det (sP (pY B)) := by
  first | exact @GlobalTheory.PolarU.jacobian_action_p | exact GlobalTheory.PolarU.jacobian_action_p | (intros; apply GlobalTheory.PolarU.jacobian_action_p <;> assumption)

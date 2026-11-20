import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnipotentMapContinuousMulDetOneCompactSuppo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBlockUnipotentMapContinuousMulDetOneCompactSuppo.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.blockUnipotentMap_continuous_mul_det_one_compactSupport : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N a b : ℕ) (e : Fin N ≃ Fin a ⊕ Fin b) (u : (Fin a → Fin b → k) → GL (Fin N) k), (∀ X, (u X : Matrix (Fin N) (Fin N) k) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) → Continuous u ∧ (∀ X Y, u (X + Y) = u X * u Y) ∧ (∀ X, (u X : Matrix (Fin N) (Fin N) k).det = 1) ∧ ∀ f : GL (Fin N) k → ℂ, HasCompactSupport f → ∀ g h : GL (Fin N) k, HasCompactSupport (fun X => f (g * (h⁻¹ * u X * h))) := by
  first | exact @GlobalTheory.blockUnipotent_props | exact GlobalTheory.blockUnipotent_props | (intros; apply GlobalTheory.blockUnipotent_props <;> assumption)

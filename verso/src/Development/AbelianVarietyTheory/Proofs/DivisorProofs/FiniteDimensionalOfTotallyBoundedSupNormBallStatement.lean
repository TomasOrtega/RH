import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfTotallyBoundedSupNormBall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.finiteDimensional_of_totallyBounded_supBall` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteDimensionalOfTotallyBoundedSupNormBall.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.finiteDimensional_of_totallyBounded_supNormBall : ∀ (T : Type) (V : Submodule ℂ (T → ℂ)) (B : Set T), (∀ φ ∈ V, (∀ x ∈ B, φ x = 0) → φ = 0) → (∀ φ ∈ V, ∃ M : ℝ, ∀ x ∈ B, ‖φ x‖ ≤ M) → (∀ ε : ℝ, 0 < ε → ∃ F : Finset (T → ℂ), ∀ φ ∈ V, (∀ x ∈ B, ‖φ x‖ ≤ 1) → ∃ ψ ∈ F, ∀ x ∈ B, ‖φ x - ψ x‖ ≤ ε) → FiniteDimensional ℂ V := by
  first | exact @GlobalTheory.finiteDimensional_of_totallyBounded_supBall | exact GlobalTheory.finiteDimensional_of_totallyBounded_supBall | (intros; apply GlobalTheory.finiteDimensional_of_totallyBounded_supBall <;> assumption)

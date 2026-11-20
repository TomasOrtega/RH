import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelParabolicTransformPhase
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Phase.ParabValues.values_parabolic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSiegelThetaTransformation%2FSiegelParabolicTransformPhase.lean&line=116#L116)
-/
theorem _root_.GlobalTheory.T.siegelParabolic_transform_values_rootOfUnity : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], Even (Fintype.card κ) → ∀ σ ∈ Matrix.symplecticGroup ι ℚ, σ.toBlocks₂₁ = 0 → ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB φ → IsSB ψ → TransS σ φ ψ → ∀ y, ∃ (u : ℂ) (y' : Matrix κ ι ℚ), Ph u ∧ ψ y = u * φ y' := by
  first | exact @GlobalTheory.Phase.ParabValues.values_parabolic | exact GlobalTheory.Phase.ParabValues.values_parabolic | (intros; apply GlobalTheory.Phase.ParabValues.values_parabolic <;> assumption)

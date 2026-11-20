import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticEqParabolicJParabolicJParabolic
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSiegelThetaTransformation%2FSymplecticEqParabolicJParabolicJParabolic.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.symplectic_eq_parabolic_J_parabolic_J_parabolic' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → ∃ p₁ ∈ Matrix.symplecticGroup ι ℚ, ∃ p₂ ∈ Matrix.symplecticGroup ι ℚ, ∃ p₃ ∈ Matrix.symplecticGroup ι ℚ, p₁.toBlocks₂₁ = 0 ∧ p₂.toBlocks₂₁ = 0 ∧ p₃.toBlocks₂₁ = 0 ∧ σ = p₁ * Matrix.J ι ℚ * p₂ * Matrix.J ι ℚ * p₃ := by
  first | exact @GlobalTheory.SW.symplectic_eq_parabolic_J_parabolic_J_parabolic | exact GlobalTheory.SW.symplectic_eq_parabolic_J_parabolic_J_parabolic | (intros; apply GlobalTheory.SW.symplectic_eq_parabolic_J_parabolic_J_parabolic <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsCosetQuadraticPhaseTestFunctionConjCharacterMu
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSiegelThetaTransformation%2FIsCosetQuadraticPhaseTestFunctionConjCharacterMu.lean&line=215#L215)
-/
theorem _root_.GlobalTheory.T.isCosetQuadraticPhaseTestFunction_conj_character_mul : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], ∀ φ : Matrix κ ι ℚ → ℂ, Shape φ → Shape (fun x => conj (φ x)) ∧ (∀ y, Shape (fun x => φ x * chr y x)) ∧ ∀ ψ, Shape ψ → Shape (fun x => φ x * ψ x) := by
  first | exact @GlobalTheory.Phase.shape_conj_chr_mul | exact GlobalTheory.Phase.shape_conj_chr_mul | (intros; apply GlobalTheory.Phase.shape_conj_chr_mul <;> assumption)

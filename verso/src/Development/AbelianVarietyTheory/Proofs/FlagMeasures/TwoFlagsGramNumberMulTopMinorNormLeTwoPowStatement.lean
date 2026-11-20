import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberMulTopMinorNormLeTwoPow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FTwoFlagsGramNumberMulTopMinorNormLeTwoPow.lean&line=279#L279)
-/
theorem _root_.GlobalTheory.T.twoFlagsGramNumber_mul_topMinorNorm_le_two_pow : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (γ : Mat k r), TwoFl k r z z' γ → ∀ x ∈ GG k r, Yv k r z z' γ x * Yv k r z' z γ⁻¹ (γ * x) * Dr k r z z' γ ≤ 2 ^ r := by
  first | exact @GlobalTheory.Amp.LemA.Yv_mul_Yv_mul_Dr_le | exact GlobalTheory.Amp.LemA.Yv_mul_Yv_mul_Dr_le | (intros; apply GlobalTheory.Amp.LemA.Yv_mul_Yv_mul_Dr_le <;> assumption)

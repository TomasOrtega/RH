import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCharacterOfFDRepMemCyclotomicAdjoin
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FIsCharacterOfFDRepMemCyclotomicAdjoin.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.isCharacterOfFDRep_mem_cyclotomic_adjoin : ∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ) (N : ℕ), 0 < N → Nat.card G ∣ N → IsChar χ → ∀ x, χ x ∈ IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))} := by
  first | exact @GlobalTheory.GLm.isChar_mem_adjoin_exp | exact GlobalTheory.GLm.isChar_mem_adjoin_exp | (intros; apply GlobalTheory.GLm.isChar_mem_adjoin_exp <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqEqOfPosCoeffEq
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FModularFormCoeffSeqEqOfPosCoeffEq.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.modularFormCoeffSeq_eq_of_pos_coeff_eq : ∀ (k L : ℕ) (χ : ℤ → ℂ) (a b : ℕ → ℂ), 1 ≤ k → 0 < L → MF k L χ a → MF k L χ b → (∀ n, n ≠ 0 → a n = b n) → a = b := by
  first | exact @GlobalTheory.EisM.eq_of_coeff_pos_eq | exact GlobalTheory.EisM.eq_of_coeff_pos_eq | (intros; apply GlobalTheory.EisM.eq_of_coeff_pos_eq <;> assumption)

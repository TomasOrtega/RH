import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormGammaOneOfCoeffSeq
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FModularFormGammaOneOfCoeffSeq.lean&line=136#L136)
-/
theorem _root_.GlobalTheory.T.modularForm_gammaOne_of_coeffSeq : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), 0 < L → N ∣ L → MF k L (ch ε) a → ∃ f : ModularForm (Gamma1 L) (k : ℤ), ⇑f = qs a := by
  first | exact @GlobalTheory.EisM.modularForm_gammaOne_of_MF | exact GlobalTheory.EisM.modularForm_gammaOne_of_MF | (intros; apply GlobalTheory.EisM.modularForm_gammaOne_of_MF <;> assumption)

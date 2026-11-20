import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralSelfNeZeroCuspForm
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FHalfPeterssonIntegralSelfNeZeroCuspForm.lean&line=70#L70)
-/
theorem _root_.GlobalTheory.T.halfPeterssonIntegral_self_ne_zero_cuspForm : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (h : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L → Wt L ρ → CF k L (ch ε) h → h ≠ 0 → pet k ρ (qs h) (qs h) ≠ 0 := by
  first | exact @GlobalTheory.EisM.PetPos.pet_self_ne_zero | exact GlobalTheory.EisM.PetPos.pet_self_ne_zero | (intros; apply GlobalTheory.EisM.PetPos.pet_self_ne_zero <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableQExpansionOfCoeffPolynomialGrowth
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EisM.qs_mdifferentiable` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FMdifferentiableQExpansionOfCoeffPolynomialGrowth.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.mdifferentiable_qExpansion_of_coeffPolynomialGrowth : ∀ a : ℕ → ℂ, PolyB a → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (qs a) := by
  first | exact @GlobalTheory.EisM.qs_mdifferentiable | exact GlobalTheory.EisM.qs_mdifferentiable | (intros; apply GlobalTheory.EisM.qs_mdifferentiable <;> assumption)

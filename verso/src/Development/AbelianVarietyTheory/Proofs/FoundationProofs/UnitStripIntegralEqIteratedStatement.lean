import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitStripIntegralEqIterated
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FUnitStripIntegralEqIterated.lean&line=102#L102)
-/
theorem _root_.GlobalTheory.T.unitStrip_integral_eq_iterated : (∀ F : ℍ → ENNReal, Measurable F → ∫⁻ τ in strip, F τ = ∫⁻ y in Set.Ioi (0 : ℝ), (∫⁻ x in Set.Ico (0 : ℝ) 1, F (ofComplex (x + y * Complex.I))) * ENNReal.ofReal (1 / y ^ 2)) ∧ ∀ F : ℍ → ℂ, IntegrableOn F strip → ∫ τ in strip, F τ = ∫ y in Set.Ioi (0 : ℝ), (∫ x in (0 : ℝ)..1, F (ofComplex (x + y * Complex.I))) / (y : ℂ) ^ 2 := by
  first | exact @GlobalTheory.EisM.strip_iterated | exact GlobalTheory.EisM.strip_iterated | (intros; apply GlobalTheory.EisM.strip_iterated <;> assumption)

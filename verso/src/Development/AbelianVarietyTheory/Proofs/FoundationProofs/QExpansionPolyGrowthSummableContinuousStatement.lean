import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionPolyGrowthSummableContinuous
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EisM.qs_summable_continuous` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FQExpansionPolyGrowthSummableContinuous.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.qExpansion_polyGrowth_summable_continuous : ∀ a : ℕ → ℂ, PolyB a → (∀ τ : ℍ, Summable fun n : ℕ => ‖a n * cexp (2 * π * Complex.I * n * τ)‖) ∧ Continuous (qs a) := by
  first | exact @GlobalTheory.EisM.qs_summable_continuous | exact GlobalTheory.EisM.qs_summable_continuous | (intros; apply GlobalTheory.EisM.qs_summable_continuous <;> assumption)

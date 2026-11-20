import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableRegularizedEisensteinLatticeTerm
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LatSumZ.latsum_summable` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSummableRegularizedEisensteinLatticeTerm.lean&line=103#L103)
-/
theorem _root_.GlobalTheory.T.summable_regularizedEisensteinLatticeTerm : ∀ (j L : ℕ) (v : ℤ × ℤ) (τ : ℍ), 1 ≤ j → 0 < L → Summable fun x => ‖dif L v (dif L v (fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2))) x‖ := by
  first | exact @GlobalTheory.LatSumZ.latsum_summable | exact GlobalTheory.LatSumZ.latsum_summable | (intros; apply GlobalTheory.LatSumZ.latsum_summable <;> assumption)

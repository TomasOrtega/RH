import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeTOperatorQExpansionSlashSum
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EisM.qs_To_hsum` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FCoeffHeckeTOperatorQExpansionSlashSum.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.coeffHeckeTOperator_qExpansion_slashSum : ∀ (k q : ℕ) (ε : ℤ → ℂ) (a : ℕ → ℂ), 1 ≤ k → 0 < q → ε 1 = 1 → PolyB a → PolyB (To k (ε q) q a) ∧ qs (To k (ε q) q a) = hsum k ε (repT q) (qs a) := by
  first | exact @GlobalTheory.EisM.qs_To_hsum | exact GlobalTheory.EisM.qs_To_hsum | (intros; apply GlobalTheory.EisM.qs_To_hsum <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraCocyclesGammaOneGammaZeroFiniteDim
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KZ.H3.lev_fd` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FEichlerShimuraCocyclesGammaOneGammaZeroFiniteDim.lean&line=72#L72)
-/
theorem _root_.GlobalTheory.T.eichlerShimuraCocycles_gammaOneGammaZero_finiteDimensional : ∀ (N l w : ℕ), 0 < N → 0 < l → FiniteDimensional ℂ (GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) w) := by
  first | exact @GlobalTheory.KZ.H3.lev_fd | exact GlobalTheory.KZ.H3.lev_fd | (intros; apply GlobalTheory.KZ.H3.lev_fd <;> assumption)

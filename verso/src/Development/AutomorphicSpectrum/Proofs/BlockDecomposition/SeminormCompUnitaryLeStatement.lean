import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeminormCompUnitaryLe
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.ComplexMatrixMajorantIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulCIff
open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSeminormCompUnitaryLe.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.seminorm_comp_unitary_le : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ κ : Matrix (Fin 2) (Fin 2) ℂ, κ * κᴴ = 1 →
    ∀ f : SchwartzMap (Fin 2 → ℂ) ℂ, ∃ f' : SchwartzMap (Fin 2 → ℂ) ℂ,
      (∀ v, f' v = f (Matrix.vecMul v κ)) ∧ pS N f' ≤ C * pS N f := by
  first | exact @GlobalTheory.CompanionTheory.UnitaryCompSchwartz.comp_unitary_bounded | exact GlobalTheory.CompanionTheory.UnitaryCompSchwartz.comp_unitary_bounded | (intros; apply GlobalTheory.CompanionTheory.UnitaryCompSchwartz.comp_unitary_bounded <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFourierBoundSeminorm
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.ComplexMatrixMajorantIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulCIff
open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPartialFourierBoundSeminorm.lean&line=177#L177)
-/
theorem _root_.GlobalTheory.T.partial_fourier_bound_seminorm : ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (f : SchwartzMap (Fin 2 → ℂ) ℂ) (x ξ : ℂ),
    ‖sF f x ξ‖ ≤ C * pS N f * (dd x * dd ξ) := by
  first | exact @GlobalTheory.CompanionTheory.GodementFE.Unif.sF_decay_unif | exact GlobalTheory.CompanionTheory.GodementFE.Unif.sF_decay_unif | (intros; apply GlobalTheory.CompanionTheory.GodementFE.Unif.sF_decay_unif <;> assumption)

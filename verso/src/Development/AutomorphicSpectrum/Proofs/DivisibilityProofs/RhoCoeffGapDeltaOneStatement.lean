import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RhoCoeffGapDeltaOne
import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsChainFirst
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Top.FlDeg.coeff_rhoM_gapDelta` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FRhoCoeffGapDeltaOne.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.rho_coeff_gap_delta_one : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ), coeff (rhoM Ψ N) (gapDelta Ψ N) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.FlDeg.coeff_rhoM_gapDelta | exact GlobalTheory.CompanionTheory.Ar.Top.FlDeg.coeff_rhoM_gapDelta | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.FlDeg.coeff_rhoM_gapDelta <;> assumption)

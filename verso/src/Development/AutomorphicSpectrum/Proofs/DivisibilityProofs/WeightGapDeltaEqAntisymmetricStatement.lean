import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.WeightGapDeltaEqAntisymmetric
import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsChainFirst
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FWeightGapDeltaEqAntisymmetric.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.weight_gap_delta_eq_antisymmetric : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ), PB.toWt (gapDelta Ψ N) = GroundTheory.Heights₂.Heights.antisymDelta Ψ N := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.FlDeg.toWt_gapDelta_eq_antisymDelta | exact GlobalTheory.CompanionTheory.Ar.Top.FlDeg.toWt_gapDelta_eq_antisymDelta | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.FlDeg.toWt_gapDelta_eq_antisymDelta <;> assumption)

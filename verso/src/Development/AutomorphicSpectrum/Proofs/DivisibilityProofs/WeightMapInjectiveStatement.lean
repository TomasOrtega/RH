import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.WeightMapInjective
import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsChainFirst
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FWeightMapInjective.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.weight_map_injective : ∀ (Ψ : Type) (N : ℕ), Function.Injective (PB.toWt : MvPolynomial (Ψ × Fin N) ℝ →ₐ[ℝ] MvPolynomial (Ψ × Fin N) ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.FlDeg.toWt_leftInverse_injective | exact GlobalTheory.CompanionTheory.Ar.Top.FlDeg.toWt_leftInverse_injective | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.FlDeg.toWt_leftInverse_injective <;> assumption)

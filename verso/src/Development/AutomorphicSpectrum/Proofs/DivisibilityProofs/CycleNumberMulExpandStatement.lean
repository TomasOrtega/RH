import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleNumberMulExpand
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Num.cycNum_mul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FCycleNumberMulExpand.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.cycle_number_mul_expand : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (Z : Ideal (MRing ι O) → ℤ) (cls : σ → K → ℤ) (H G : MvPolynomial σ ℝ) (Q : List (K → ℤ)), cycNum Z cls (H * G) Q = ∑ μ ∈ G.support, G.coeff μ * cycNum Z cls H (classList cls μ ++ Q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.cycNum_mul | exact GlobalTheory.CompanionTheory.Ar.Num.cycNum_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.cycNum_mul <;> assumption)

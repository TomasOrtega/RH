import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PshDoublePositivePotential
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitTTop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogRatio
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Giv.Mix.TwicePos.isPsh_add_zero_add` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FPshDoublePositivePotential.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.psh_double_positive_potential : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (Θ : LocPot X), IsPotential A Θ → IsPosPot A Θ → IsPsh A (Θ + LocPot.ofFun (fun _ => (0 : ℝ)) + Θ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Mix.TwicePos.isPsh_add_zero_add | exact GlobalTheory.CompanionTheory.Ar.Giv.Mix.TwicePos.isPsh_add_zero_add | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Mix.TwicePos.isPsh_add_zero_add <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistIsMultiHomogIdeal
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FTwistIsMultiHomogIdeal.lean&line=89#L89)
-/
theorem _root_.GlobalTheory.T.twist_isMultiHomogIdeal : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (W : Ideal (MRing ι)), IsMultiHomogIdeal W → IsMultiHomogIdeal (twist p W) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.isMultiHomogIdeal_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.isMultiHomogIdeal_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.isMultiHomogIdeal_twist <;> assumption)

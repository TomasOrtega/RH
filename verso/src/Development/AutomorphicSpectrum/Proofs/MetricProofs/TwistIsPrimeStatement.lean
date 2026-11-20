import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistIsPrime
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FTwistIsPrime.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.twist_isPrime_of_isPrime_of_noRoot : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (W : Ideal (MRing ι)), W.IsPrime → NoRoot p W → (twist p W).IsPrime := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.twist_isPrime | exact GlobalTheory.CompanionTheory.Ar.Tw.twist_isPrime | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.twist_isPrime <;> assumption)

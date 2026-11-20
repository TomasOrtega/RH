import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwLineSmoothConjInvariantGlue
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FTwLineSmoothConjInvariantGlue.lean&line=160#L160)
-/
theorem _root_.GlobalTheory.T.twLine_smooth_conjInvariant_glue : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (A : HermLine ι), p ≠ 0 → (IsSmoothHerm A → IsSmoothHerm (twLine p A)) ∧ (IsSmoothHerm A → IsSmoothHerm (conjLine A)) ∧ IsConjInvariantH (twLine p A) ∧ (∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (twLine p A).h (glue z (vPlus p)) = A.h z) ∧ (∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (twLine p A).h (glue z (vMinus p)) = (conjLine A).h z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.Lines.twLine_main | exact GlobalTheory.CompanionTheory.Ar.Tw.Lines.twLine_main | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.Lines.twLine_main <;> assumption)

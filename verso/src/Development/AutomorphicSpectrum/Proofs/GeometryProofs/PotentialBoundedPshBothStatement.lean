import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PotentialBoundedPshBoth
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SectionBoundaryClosedAndCodense
open GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FPotentialBoundedPshBoth.lean&line=212#L212)
-/
theorem _root_.GlobalTheory.T.potential_bounded_psh_both : ∀ (e : ℕ) (σ : Type) (S : PB.AnSys e σ) (a : σ), (∀ t, ReciprocityTheory.AnForm.M.IsPsh S.A ((S.potT a t).rsmul (-1)) ∧ ReciprocityTheory.AnForm.M.IsPsh S.A (S.potT a t)) → ∃ C : ℝ, ∀ t, 0 < t → t ≤ S.t₀ → ∀ x, |S.phT a t x| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlatBound.flat_phT_bounded | exact GlobalTheory.CompanionTheory.Ar.FlatBound.flat_phT_bounded | (intros; apply GlobalTheory.CompanionTheory.Ar.FlatBound.flat_phT_bounded <;> assumption)

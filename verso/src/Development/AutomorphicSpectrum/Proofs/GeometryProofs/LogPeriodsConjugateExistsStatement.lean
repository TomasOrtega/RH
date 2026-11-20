import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodsConjugateExists
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DifferentiableOnStarStar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FLogPeriodsConjugateExists.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.log_periods_conjugate_exists : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L' : Flat.LogPeriods n a g Λ), ∃ L : Flat.LogPeriods n a g Λ, (∀ w x, L.P w x = star (L'.P (star w) x)) ∧ ∀ z, L.H z = (L'.H (star z)).map (starRingEnd ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LogPer.exists_conj_logPeriods | exact GlobalTheory.CompanionTheory.Ar.Flat.LogPer.exists_conj_logPeriods | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LogPer.exists_conj_logPeriods <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeSeriesDerivativeGrowthBound
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FConeSeriesDerivativeGrowthBound.lean&line=107#L107)
-/
theorem _root_.GlobalTheory.T.cone_series_derivative_growth_bound : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (B R : ℕ) (β : ι → ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ‖s‖ ≤ R → -(B : ℝ) ≤ s.re →
  ∀ x : Fin r → ℝ, (∀ i, 0 ≤ x i) →
    ‖Fr a b s β x‖ ≤ C * sizeE x ^ ((Fintype.card ι : ℤ) * (B : ℤ) - ∑ j, (β j : ℤ)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.baseBound | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.baseBound | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.baseBound <;> assumption)

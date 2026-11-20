import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeTilingBySignRegions
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FConeTilingBySignRegions.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.cone_values_negative_integer_rational : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (p : ℕ), (∀ m : Fin r → ℕ, ∃ q : ℚ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (q : ℝ)) →
  ∀ cs : List (Fin r), ∃ ρ : (Fin r → ℕ) → ℚ, ∀ m, DL cs (coneTerm a b (-(p : ℂ))) m = (ρ m : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_neg_nat_rational | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_neg_nat_rational | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_neg_nat_rational <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeValuesNegativeIntegerRational
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_neg_natCast_eq_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FConeValuesNegativeIntegerRational.lean&line=128#L128)
-/
theorem _root_.GlobalTheory.T.high_difference_vanishes_negative_integer : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (cs : List (Fin r)) (i : Fin r) (N p : ℕ), cs.count i = N → Fintype.card ι * p < N →
  ∀ m, DL cs (coneTerm a b (-(p : ℂ))) m = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_neg_natCast_eq_zero | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_neg_natCast_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_neg_natCast_eq_zero <;> assumption)

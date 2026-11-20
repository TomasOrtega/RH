import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightedSumDecompositionDenominators
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Integral.expansion_all_variables_int` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWeightedSumDecompositionDenominators.lean&line=195#L195)
-/
theorem _root_.GlobalTheory.T.weighted_sum_decomposition_denominators : ∀ (r l N : ℕ) (w : (Fin r → ℕ) → ℚ), 0 < l → GoodWeight l w → (∀ m, ∃ z : ℤ, w m = z) → ∃ (Q : Type) (_ : Fintype Q) (cs : Q → List (Fin r)) (u : Q → (Fin r → ℕ) → ℚ) (K : ℕ), (∀ q, BddW (u q)) ∧ (∀ q i, (cs q).count i = N ∨ ∀ m, m i ≠ 0 → u q m = 0) ∧ (∀ q m, ∃ z : ℤ, (l : ℚ) ^ K * u q m = z) ∧ ∀ g : (Fin r → ℕ) → ℂ, Summable g → ∑' m, (w m : ℂ) * g m = ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) g m := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Integral.expansion_all_variables_int | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Integral.expansion_all_variables_int | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Integral.expansion_all_variables_int <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDifferenceConeTermEq
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_eq_DLR` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FFiniteDifferenceConeTermEq.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.finite_difference_cone_term_eq : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (s : ℂ) (cs : List (Fin r)) (m : Fin r → ℕ),
  DL cs (coneTerm a b s) m = DLR cs (Fr a b s 0) (fun i => (m i : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_eq_DLR | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_eq_DLR | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_eq_DLR <;> assumption)

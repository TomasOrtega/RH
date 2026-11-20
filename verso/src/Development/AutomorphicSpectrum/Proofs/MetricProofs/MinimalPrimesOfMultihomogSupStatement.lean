import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinimalPrimesOfMultihomogSup
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Cmp.MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FMinimalPrimesOfMultihomogSup.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.minimal_primes_of_multihomog_sup : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)), IsMultiHomogIdeal P → IsMultiHomogIdeal D → ∀ Q ∈ (P ⊔ D).minimalPrimes, IsMultiHomogIdeal Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup | exact GlobalTheory.CompanionTheory.Ar.Cmp.MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup <;> assumption)

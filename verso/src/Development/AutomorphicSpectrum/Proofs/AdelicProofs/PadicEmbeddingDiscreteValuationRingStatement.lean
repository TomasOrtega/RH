import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicEmbeddingDiscreteValuationRing
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Fl.ValRing.exists_dvr_of_padic_embedding` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAdelicProofs%2FPadicEmbeddingDiscreteValuationRing.lean&line=137#L137)
-/
theorem _root_.GlobalTheory.T.padic_embedding_discrete_valuation_ring : ∀ (K : Type) [Field K] [NumberField K] (p : Nat.Primes) (j : K →+* ℂ_[p]), ∃ (V : ValuationSubring K), IsDiscreteValuationRing V ∧ (∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ V) ∧ (∀ a : 𝓞 K, (a : K) ∈ V) ∧ ∀ n : ℕ, ¬ (p : ℕ) ∣ n → ‖j (n : K)‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.ValRing.exists_dvr_of_padic_embedding | exact GlobalTheory.CompanionTheory.Ar.Fl.ValRing.exists_dvr_of_padic_embedding | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.ValRing.exists_dvr_of_padic_embedding <;> assumption)

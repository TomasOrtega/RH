import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeElementCongruent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.NormPrimes.exists_prime_norm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsPrimeElementCongruent.lean&line=68#L68)
-/
theorem _root_.GlobalTheory.T.exists_prime_element_congruent : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), M ≠ 0 → ∀ (a : 𝓞 K), IsCoprime a (M : 𝓞 K) → ∀ N : ℕ, ∃ (π : 𝓞 K) (p : ℕ), p.Prime ∧ N < p ∧ Algebra.norm ℤ π = p ∧ π - a ∈ Ideal.span {(M : 𝓞 K)} := by
  first | exact @GlobalTheory.Mem.NormPrimes.exists_prime_norm | exact GlobalTheory.Mem.NormPrimes.exists_prime_norm | (intros; apply GlobalTheory.Mem.NormPrimes.exists_prime_norm <;> assumption)

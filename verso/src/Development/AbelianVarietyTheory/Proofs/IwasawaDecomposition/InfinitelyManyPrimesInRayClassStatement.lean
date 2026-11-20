import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.RayPrimes.exists_prime_in_class` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FInfinitelyManyPrimesInRayClass.lean&line=296#L296)
-/
theorem _root_.GlobalTheory.T.infinitely_many_primes_in_ray_class : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (c : D.G) (N : ℕ), ∃ v : D.Pr, D.cls v.1.asIdeal = c ∧ (Ideal.absNorm v.1.asIdeal).Prime ∧ N < Ideal.absNorm v.1.asIdeal := by
  first | exact @GlobalTheory.Mem.RayPrimes.exists_prime_in_class | exact GlobalTheory.Mem.RayPrimes.exists_prime_in_class | (intros; apply GlobalTheory.Mem.RayPrimes.exists_prime_in_class <;> assumption)

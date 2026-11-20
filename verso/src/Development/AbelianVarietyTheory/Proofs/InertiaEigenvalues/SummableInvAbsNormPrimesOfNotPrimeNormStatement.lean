import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableInvAbsNormPrimesOfNotPrimeNorm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealCharacterLContinuationNeZeroOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FSummableInvAbsNormPrimesOfNotPrimeNorm.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.summable_inv_absNorm_primes_of_not_prime_norm : ∀ (K : Type) [Field K] [NumberField K], Summable fun P : {P : HeightOneSpectrum (𝓞 K) // ¬ (Ideal.absNorm P.asIdeal).Prime} => ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ)⁻¹ := by
  first | exact @GlobalTheory.summable_inv_absNorm_of_not_prime | exact GlobalTheory.summable_inv_absNorm_of_not_prime | (intros; apply GlobalTheory.summable_inv_absNorm_of_not_prime <;> assumption)

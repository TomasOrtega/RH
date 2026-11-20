import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeNormCyclotomicCharNeOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealCharacterLContinuationNeZeroOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NormChar.exists_prime_norm_char_ne_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsPrimeNormCyclotomicCharNeOne.lean&line=75#L75)
-/
theorem _root_.GlobalTheory.T.exists_prime_norm_cyclotomicChar_ne_one : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → Irreducible (cyclotomic m K) → ∀ χ : (ZMod m)ˣ →* ℂˣ, χ ≠ 1 → ∃ (P : HeightOneSpectrum (𝓞 K)) (u : (ZMod m)ˣ), (u : ZMod m) = (Ideal.absNorm P.asIdeal : ℕ) ∧ χ u ≠ 1 := by
  first | exact @GlobalTheory.NormChar.exists_prime_norm_char_ne_one | exact GlobalTheory.NormChar.exists_prime_norm_char_ne_one | (intros; apply GlobalTheory.NormChar.exists_prime_norm_char_ne_one <;> assumption)

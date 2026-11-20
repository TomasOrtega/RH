import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NcardPrimesOverEqFinrankOfTrivialFrobenius
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_finite_ncard_primesOver_eq_finrank_of_pow_absNorm_sub_mem` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FNcardPrimesOverEqFinrankOfTrivialFrobenius.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.ncard_primesOver_eq_finrank_of_trivial_frobenius : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M], ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → (∀ P ∈ v.asIdeal.primesOver (𝓞 M), ∀ x : 𝓞 M, x ^ Ideal.absNorm v.asIdeal - x ∈ P) → (v.asIdeal.primesOver (𝓞 M)).ncard = Module.finrank K M ∧ ∀ P ∈ v.asIdeal.primesOver (𝓞 M), Ideal.absNorm P = Ideal.absNorm v.asIdeal := by
  first | exact @GlobalTheory.exists_finite_ncard_primesOver_eq_finrank_of_pow_absNorm_sub_mem | exact GlobalTheory.exists_finite_ncard_primesOver_eq_finrank_of_pow_absNorm_sub_mem | (intros; apply GlobalTheory.exists_finite_ncard_primesOver_eq_finrank_of_pow_absNorm_sub_mem <;> assumption)

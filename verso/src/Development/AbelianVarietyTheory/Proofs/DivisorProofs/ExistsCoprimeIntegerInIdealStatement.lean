import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeIntegerInIdeal
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NormCoprime.exists_coprime_mem` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCoprimeIntegerInIdeal.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.exists_coprime_integer_in_ideal : ∀ (K : Type) [Field K] [NumberField K] (c : Ideal (𝓞 K)) (l : ℕ), l.Prime → c ≠ ⊥ →
    (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ c → (l : 𝓞 K) ∉ v.asIdeal) → ∃ m : ℕ, m.Coprime l ∧ (m : 𝓞 K) ∈ c := by
  first | exact @GlobalTheory.NormCoprime.exists_coprime_mem | exact GlobalTheory.NormCoprime.exists_coprime_mem | (intros; apply GlobalTheory.NormCoprime.exists_coprime_mem <;> assumption)

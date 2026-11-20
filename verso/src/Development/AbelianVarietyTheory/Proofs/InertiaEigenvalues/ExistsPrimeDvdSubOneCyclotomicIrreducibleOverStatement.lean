import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeDvdSubOneCyclotomicIrreducibleOver
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsPrimeDvdSubOneCyclotomicIrreducibleOver.lean&line=88#L88)
-/
theorem _root_.GlobalTheory.T.exists_prime_dvd_sub_one_cyclotomic_irreducible_over : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), n ≠ 0 → ∃ m : ℕ, m.Prime ∧ n ∣ m - 1 ∧ Irreducible (cyclotomic m K) := by
  first | exact @GlobalTheory.exists_prime_dvd_sub_one_irreducible_cyclotomic | exact GlobalTheory.exists_prime_dvd_sub_one_irreducible_cyclotomic | (intros; apply GlobalTheory.exists_prime_dvd_sub_one_irreducible_cyclotomic <;> assumption)

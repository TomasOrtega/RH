import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArithmeticLargeSieveOneResidueClassPerPrime
import Mathlib
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FArithmeticLargeSieveOneResidueClassPerPrime.lean&line=427#L427)
-/
theorem _root_.GlobalTheory.T.arithmeticLargeSieve_one_residue_class_per_prime : ∀ (M N Q q : ℕ) (S : Finset ℕ), 1 ≤ Q → 1 ≤ q → S ⊆ Finset.Ioc M (M + N) → (∀ p : ℕ, p.Prime → p ≤ Q → ¬ p ∣ q → ∃ c : ℕ, ∀ n ∈ S, ¬ n ≡ c [MOD p]) → (S.card : ℝ) * ((q.totient : ℝ) / q * Real.log Q) ≤ (Q : ℝ) ^ 2 + 2 * Real.pi * N := by
  first | exact @GlobalTheory.arithmetic_large_sieve_one_class | exact GlobalTheory.arithmetic_large_sieve_one_class | (intros; apply GlobalTheory.arithmetic_large_sieve_one_class <;> assumption)

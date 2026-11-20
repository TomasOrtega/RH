import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulMemRangePiQuotientMinimalPrimes
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsNatMulMemRangePiQuotientMinimalPrimes.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.exists_nat_mul_mem_range_pi_quotient_minimalPrimes' : ∀ (B : Type) [CommRing B] [Module.Finite ℤ B], ∃ n : ℕ, n ≠ 0 ∧ ∀ b' : ((P : minimalPrimes B) → B ⧸ (P : Ideal B)), (n : (P : minimalPrimes B) → B ⧸ (P : Ideal B)) * b' ∈ (Pi.ringHom fun P : minimalPrimes B => Ideal.Quotient.mk (P : Ideal B)).range := by
  first | exact @GlobalTheory.CokerMinimalPrimes.exists_nat_mul_mem_range_pi_quotient_minimalPrimes | exact GlobalTheory.CokerMinimalPrimes.exists_nat_mul_mem_range_pi_quotient_minimalPrimes | (intros; apply GlobalTheory.CokerMinimalPrimes.exists_nat_mul_mem_range_pi_quotient_minimalPrimes <;> assumption)

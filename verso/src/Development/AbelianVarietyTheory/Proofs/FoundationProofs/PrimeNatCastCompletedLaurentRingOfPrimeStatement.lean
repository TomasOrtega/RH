import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeNatCastCompletedLaurentRingOfPrime
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.K5.prime_natCast_completedLaurentRing_of_prime` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FPrimeNatCastCompletedLaurentRingOfPrime.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.prime_natCast_completed_laurent_ring : ∀ (p : ℕ) [Fact p.Prime], Prime (p : O0 p) := by
  first | exact @GlobalTheory.K5.prime_natCast_completedLaurentRing_of_prime | exact GlobalTheory.K5.prime_natCast_completedLaurentRing_of_prime | (intros; apply GlobalTheory.K5.prime_natCast_completedLaurentRing_of_prime <;> assumption)

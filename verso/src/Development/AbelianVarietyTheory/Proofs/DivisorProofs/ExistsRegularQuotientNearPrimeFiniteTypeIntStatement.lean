import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularQuotientNearPrimeFiniteTypeInt
import Mathlib
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsRegularQuotientNearPrimeFiniteTypeInt.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_regular_quotient_near_prime_finiteType_int : ∀ (B : Type) [CommRing B] [Algebra.FiniteType ℤ B] (p : Ideal B) [p.IsPrime], ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) := by
  first | exact @GlobalTheory.generically_regular_quotient_of_finiteType_int | exact GlobalTheory.generically_regular_quotient_of_finiteType_int | (intros; apply GlobalTheory.generically_regular_quotient_of_finiteType_int <;> assumption)

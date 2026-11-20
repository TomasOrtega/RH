import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeIsIntegralOverStandardLatticeStabilis
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NormSum.exists_prime_integralOver` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsPrimeIsIntegralOverStandardLatticeStabilis.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.exists_prime_isIntegralOverStandardLatticeStabiliser : ∀ (D : Formalism.BasicNotions.D7) (N : ℕ) (h : ↥(Formalism.MainNotions.StandardLatticesGL3.GA D N)), ∃ p : ℕ, p.Prime ∧ GlobalTheory.NormSum.IntegralOver D p h := by
  first | exact @GlobalTheory.NormSum.exists_prime_integralOver | exact GlobalTheory.NormSum.exists_prime_integralOver | (intros; apply GlobalTheory.NormSum.exists_prime_integralOver <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimeSpanOfSqEqNegPrime
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CMModel.isPrime_span_of_sq_eq_neg_prime` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsPrimeSpanOfSqEqNegPrime.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.isPrime_span_of_sq_eq_neg_prime_quadratic : ∀ (p : ℕ) (K : Type) [Field K] [NumberField K] (y : 𝓞 K), p.Prime → Module.finrank ℚ K = 2 → y ^ 2 = -(p : 𝓞 K) → (Ideal.span {y}).IsPrime := by
  first | exact @GlobalTheory.CMModel.isPrime_span_of_sq_eq_neg_prime | exact GlobalTheory.CMModel.isPrime_span_of_sq_eq_neg_prime | (intros; apply GlobalTheory.CMModel.isPrime_span_of_sq_eq_neg_prime <;> assumption)

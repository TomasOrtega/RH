import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqAlgebraMapOfIntegralAtHeightOnePrimes
open scoped BigOperators Matrix ComplexConjugate
open Polynomial
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsEqAlgebraMapOfIntegralAtHeightOnePrimes.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_eq_algebraMap_of_integral_at_height_one_primes : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (t : FractionRing R), (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → ∃ a b : R, b ∉ p ∧ t * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a) → ∃ a : R, algebraMap R (FractionRing R) a = t := by
  first | exact @GlobalTheory.integral_of_forall_height_one | exact GlobalTheory.integral_of_forall_height_one | (intros; apply GlobalTheory.integral_of_forall_height_one <;> assumption)

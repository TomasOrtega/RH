import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralQuotientOfValuationSubringAboveDvr
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
open GlobalTheory.Published.AbVarRed IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ValAbove.exists_integral_mul_eq_of_isAbove` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsIntegralQuotientOfValuationSubringAboveDvr.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.exists_integral_quotient_of_valuationSubring_above_dvr : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ y ∈ V, ∃ a s : Ω, ((algebraMap K Ω).comp (algebraMap R K)).IsIntegralElem a ∧ ((algebraMap K Ω).comp (algebraMap R K)).IsIntegralElem s ∧ V.valuation s = 1 ∧ y * s = a := by
  first | exact @GlobalTheory.ValAbove.exists_integral_mul_eq_of_isAbove | exact GlobalTheory.ValAbove.exists_integral_mul_eq_of_isAbove | (intros; apply GlobalTheory.ValAbove.exists_integral_mul_eq_of_isAbove <;> assumption)

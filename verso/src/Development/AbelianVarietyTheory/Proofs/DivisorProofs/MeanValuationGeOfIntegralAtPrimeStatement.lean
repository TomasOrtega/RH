import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanValuationGeOfIntegralAtPrime
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMeanValuationGeOfIntegralAtPrime.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.meanValuation_ge_of_integral_at_prime : ∀ {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {β : ℂ} {p : K[X]}, GlobalTheory.FunObj.SqNum.IsMinPol σ β p → β ≠ 0 → ∀ {c : K}, c ≠ 0 → ∀ {l : ℕ}, l.Prime → ∀ {w : Formalism.PairingDivisionLocalBalance.Pl K}, (l : 𝓞 K) ∈ w.asIdeal → ∀ {m : ℕ}, GlobalTheory.CMVal.IntAt l ((l : ℂ) ^ m * (σ c * β)) → -((m : ℝ) * (Formalism.DivisionValues.vw w (l : K) : ℝ)) ≤ (Formalism.DivisionValues.vw w c : ℝ) + GlobalTheory.FunObj.SqNum.meanVal_vw w p := by
  first | exact @GlobalTheory.FunObj.SqNum.meanVal_vw_ge_of_intAt | exact GlobalTheory.FunObj.SqNum.meanVal_vw_ge_of_intAt | (intros; apply GlobalTheory.FunObj.SqNum.meanVal_vw_ge_of_intAt <;> assumption)

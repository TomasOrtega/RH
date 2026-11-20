import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanValuationNormOverDegreeSmulEqAddValuation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Formalism.PairingDivisors.StatementH
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMeanValuationNormOverDegreeSmulEqAddValuation.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.meanValuationNormOverDegree_smul_eq_add_valuation : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (β : ℂ) (u : K) (p q : K[X]), GlobalTheory.FunObj.SqNum.IsMinPol σ β p → GlobalTheory.FunObj.SqNum.IsMinPol σ (σ u * β) q → β ≠ 0 → u ≠ 0 → ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, GlobalTheory.FunObj.SqNum.meanVal_vw w q = GlobalTheory.FunObj.SqNum.meanVal_vw w p + vw w u := by
  first | exact @GlobalTheory.FunObj.SqNum.meanVal_vw_smul | exact GlobalTheory.FunObj.SqNum.meanVal_vw_smul | (intros; apply GlobalTheory.FunObj.SqNum.meanVal_vw_smul <;> assumption)

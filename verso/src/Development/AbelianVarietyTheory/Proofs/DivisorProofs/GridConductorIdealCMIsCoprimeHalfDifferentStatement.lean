import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridConductorIdealCMIsCoprimeHalfDifferent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGridConductorIdealCMIsCoprimeHalfDifferent.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.gridConductorIdealCM_isCoprime_halfDifferent : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L), Nat.Coprime D.host.pde (D.host.QS * D.host.q) → Nat.Coprime D.host.pde' (D.host.QS * D.host.q) → IsCoprime (condE P) D.host.𝔟 := by
  first | exact @GlobalTheory.FunObj.StdDatum.HalfDiff.condE_isCoprime_bb | exact GlobalTheory.FunObj.StdDatum.HalfDiff.condE_isCoprime_bb | (intros; apply GlobalTheory.FunObj.StdDatum.HalfDiff.condE_isCoprime_bb <;> assumption)

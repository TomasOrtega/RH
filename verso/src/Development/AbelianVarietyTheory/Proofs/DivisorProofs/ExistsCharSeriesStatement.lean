import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharSeries
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCharSeries.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.exists_charSeries' : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate), ∃ u : MvPowerSeries (Fin d) O, constantCoeff u = 1 ∧ ∀ n, c.ev n u = charElem χ n := by
  first | exact @GlobalTheory.QLog.exists_charSeries | exact GlobalTheory.QLog.exists_charSeries | (intros; apply GlobalTheory.QLog.exists_charSeries <;> assumption)

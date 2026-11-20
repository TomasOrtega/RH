import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivGroupFormalChartOfConnected
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ChartEx.chart_exists` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsPDivGroupFormalChartOfConnected.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.exists_pDivGroupFormalChart_of_connected : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ G : PDivGroup p O, IsConn G → ∃ d : ℕ, Nonempty (QLog.Chart G d) := by
  first | exact @GlobalTheory.ChartEx.chart_exists | exact GlobalTheory.ChartEx.chart_exists | (intros; apply GlobalTheory.ChartEx.chart_exists <;> assumption)

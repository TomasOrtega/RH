import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdDivGroupChartFormsBasisAndDifferential
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.chart_form_basis` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPdDivGroupChartFormsBasisAndDifferential.lean&line=231#L231)
-/
theorem _root_.GlobalTheory.T.pdDivGroupChart_forms_basis_and_differential : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), Function.Bijective (Fintype.linearCombination O c.form) ∧ ∀ (n : ℕ) (f : MvPowerSeries (Fin d) O), constantCoeff f = 0 → PDiv.dUnit O (c.ev n f) = ∑ i, lin f i • PDiv.dUnit O (c.x n i) := by
  first | exact @GlobalTheory.chart_form_basis | exact GlobalTheory.chart_form_basis | (intros; apply GlobalTheory.chart_form_basis <;> assumption)

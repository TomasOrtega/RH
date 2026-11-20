import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectedPDivGroupChartOfIsConn
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Katz.exists_chart_of_isConn` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsConnectedPDivGroupChartOfIsConn.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.exists_connectedPDivGroupChart_of_isConn : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), G.IsConn → ∃ d, Nonempty (Chart G d) := by
  first | exact @GlobalTheory.Katz.exists_chart_of_isConn | exact GlobalTheory.Katz.exists_chart_of_isConn | (intros; apply GlobalTheory.Katz.exists_chart_of_isConn <;> assumption)

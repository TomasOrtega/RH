import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixSpanLeRapidSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.MeasurableCompInfGL
open Classical MeasureTheory NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMatrixSpanLeRapidSpan.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.matrix_span_le_rapid_span : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (π : GlobalTheory.CuspRep.CuspSub E a), GlobalTheory.JSW.mspan π ≤ GlobalTheory.JSW.rspan π := by
  first | exact @GlobalTheory.JSW.mspan_le_rspan | exact GlobalTheory.JSW.mspan_le_rspan | (intros; apply GlobalTheory.JSW.mspan_le_rspan <;> assumption)

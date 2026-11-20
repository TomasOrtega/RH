import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.FineJacquetSegmentLengthTwo
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LkSegFine2.fineJac_of_len_eq_two` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FWeilBound%2FCoreStatements%2FAutomorphicKernels%2FSquareIntegrableSegments%2FSegmentSubquotients%2FFineJacquetSegmentLengthTwo.lean&line=294#L294)
-/
theorem _root_.GlobalTheory.TL.fine_jacquet_segment_length_two : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation) (Δ : Segment k) (h : Δ.len = 2), FineJac Δ := by
  first | exact @GlobalTheory.CompanionTheory.LkSegFine2.fineJac_of_len_eq_two | exact GlobalTheory.CompanionTheory.LkSegFine2.fineJac_of_len_eq_two

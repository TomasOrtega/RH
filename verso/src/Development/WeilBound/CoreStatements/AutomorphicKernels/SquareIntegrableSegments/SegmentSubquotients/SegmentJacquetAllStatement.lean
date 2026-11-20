import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.SegmentJacquetAll
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.LkSegCoarse.lSegJacquet | exact GlobalTheory.CompanionTheory.LkSegCoarse.lSegJacquet`.
-/
theorem _root_.GlobalTheory.TL.segment_jacquet_all : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation), LSegJacquet k := by
  first | exact @GlobalTheory.CompanionTheory.LkSegCoarse.lSegJacquet | exact GlobalTheory.CompanionTheory.LkSegCoarse.lSegJacquet

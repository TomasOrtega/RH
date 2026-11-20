import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAll
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSegmentJacquetAll.lean&line=73#L73)
-/
theorem _root_.GlobalTheory.T.segment_jacquet_all : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation), LSegJacquet k := by
  first | exact @GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet | exact GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet | (intros; apply GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSegmentDual
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLanglandsSegmentDual.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.langlands_segment_dual : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation), LSegDual k := by
  first | exact @GlobalTheory.CompanionTheory.SegLDual.lSegDual | exact GlobalTheory.CompanionTheory.SegLDual.lSegDual | (intros; apply GlobalTheory.CompanionTheory.SegLDual.lSegDual <;> assumption)

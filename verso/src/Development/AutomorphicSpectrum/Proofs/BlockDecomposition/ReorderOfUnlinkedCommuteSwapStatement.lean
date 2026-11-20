import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReorderOfUnlinkedCommuteSwap
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BZSegReorder.reorder` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FReorderOfUnlinkedCommuteSwap.lean&line=136#L136)
-/
theorem _root_.GlobalTheory.T.reorder_of_unlinked_commute_swap : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.LUnlinkedComm k → GlobalTheory.BZSeg.SwapProd k → GlobalTheory.BZSeg.Reorder k := by
  first | exact @GlobalTheory.CompanionTheory.BZSegReorder.reorder | exact GlobalTheory.CompanionTheory.BZSegReorder.reorder | (intros; apply GlobalTheory.CompanionTheory.BZSegReorder.reorder <;> assumption)

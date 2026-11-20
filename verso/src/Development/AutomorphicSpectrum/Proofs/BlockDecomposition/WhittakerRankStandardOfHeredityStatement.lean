import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankStandardOfHeredity
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BZSeg.whitRankStd_of_heredity` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWhittakerRankStandardOfHeredity.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.whittaker_rank_standard_of_heredity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → GlobalTheory.BZSeg.WhitRankStd k := by
  first | exact @GlobalTheory.CompanionTheory.BZSeg.whitRankStd_of_heredity | exact GlobalTheory.CompanionTheory.BZSeg.whitRankStd_of_heredity | (intros; apply GlobalTheory.CompanionTheory.BZSeg.whitRankStd_of_heredity <;> assumption)

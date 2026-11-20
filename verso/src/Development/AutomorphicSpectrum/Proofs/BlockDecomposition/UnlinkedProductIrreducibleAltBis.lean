import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LUnlinkedIrr
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLUnlinkedIrr.lean&line=379#L379)
-/
theorem _root_.GlobalTheory.T.lUnlinkedIrr_of_irreducibleAdmissible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.LSegJacquet k → GlobalTheory.Published.GeometricLemmaFiltration → GlobalTheory.BZSeg.NuPair k → GlobalTheory.BZSeg.WhitRankStd k → GlobalTheory.BZSeg.ProdIrrFiniteLength k → GlobalTheory.BZSeg.LUnlinkedIrr k := by
  first | exact @GlobalTheory.CompanionTheory.BZSeg.NuPairIrr.lUnlinkedIrr | exact GlobalTheory.CompanionTheory.BZSeg.NuPairIrr.lUnlinkedIrr | (intros; apply GlobalTheory.CompanionTheory.BZSeg.NuPairIrr.lUnlinkedIrr <;> assumption)

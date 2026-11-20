import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducible
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BZSegComm.lUnlinkedComm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnlinkedCommuteOfIrreducible.lean&line=237#L237)
-/
theorem _root_.GlobalTheory.T.unlinked_commute_of_irreducible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.LUnlinkedIrr k → GlobalTheory.BZSeg.LUnlinkedComm k := by
  first | exact @GlobalTheory.CompanionTheory.BZSegComm.lUnlinkedComm | exact GlobalTheory.CompanionTheory.BZSegComm.lUnlinkedComm | (intros; apply GlobalTheory.CompanionTheory.BZSegComm.lUnlinkedComm <;> assumption)

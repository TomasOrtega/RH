import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeJacquetHolds
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.DerivJac
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BZDerivJac.derivJac_main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDerivativeJacquetHolds.lean&line=339#L339)
-/
theorem _root_.GlobalTheory.T.derivative_jacquet_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.DerivJac k := by
  first | exact @GlobalTheory.CompanionTheory.BZDerivJac.derivJac_main | exact GlobalTheory.CompanionTheory.BZDerivJac.derivJac_main | (intros; apply GlobalTheory.CompanionTheory.BZDerivJac.derivJac_main <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NuPairOfDerivativesJacquet
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.DerivSub
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BZNuPairAsm.nuPair` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNuPairOfDerivativesJacquet.lean&line=67#L67)
-/
theorem _root_.GlobalTheory.T.nu_pair_of_derivatives_jacquet : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.DerivJac k → GlobalTheory.BZSeg.JmTheta k → GlobalTheory.BZSeg.DerivSub k → GlobalTheory.BZSeg.NuPair k := by
  first | exact @GlobalTheory.CompanionTheory.BZNuPairAsm.nuPair | exact GlobalTheory.CompanionTheory.BZNuPairAsm.nuPair | (intros; apply GlobalTheory.CompanionTheory.BZNuPairAsm.nuPair <;> assumption)

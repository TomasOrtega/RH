import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFiltrationExhaustive
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BZMirExhaust.exhaust` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMirabolicFiltrationExhaustive.lean&line=98#L98)
-/
theorem _root_.GlobalTheory.T.mirabolic_filtration_exhaustive : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.Exhaust k := by
  first | exact @GlobalTheory.CompanionTheory.BZMirExhaust.exhaust | exact GlobalTheory.CompanionTheory.BZMirExhaust.exhaust | (intros; apply GlobalTheory.CompanionTheory.BZMirExhaust.exhaust <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPsiMinusExact
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BZMir.exPsiMinus` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMirabolicPsiMinusExact.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.mirabolic_psi_minus_exact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.ExPsiMinus k := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.exPsiMinus | exact GlobalTheory.CompanionTheory.BZMir.exPsiMinus | (intros; apply GlobalTheory.CompanionTheory.BZMir.exPsiMinus <;> assumption)

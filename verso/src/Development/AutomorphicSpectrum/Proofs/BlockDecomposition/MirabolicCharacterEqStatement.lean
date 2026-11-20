import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCharacterEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMirabolicCharacterEq.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.mirabolic_character_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.MirCharEq k := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.mirChar_eq_thetaA_single | exact GlobalTheory.CompanionTheory.BZMir.mirChar_eq_thetaA_single | (intros; apply GlobalTheory.CompanionTheory.BZMir.mirChar_eq_thetaA_single <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransposeInverseInvolutionApply
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTransposeInverseInvolutionApply.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.transpose_inverse_involution_apply : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (g : GL (Fin N) k), thetaW k N (thetaW k N g) = g := by
  first | exact @GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW | exact GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW | (intros; apply GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW <;> assumption)

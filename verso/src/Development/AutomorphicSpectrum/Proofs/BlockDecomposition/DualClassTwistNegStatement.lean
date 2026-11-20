import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ZcDual.dualCl_nu` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDualClassTwistNeg.lean&line=142#L142)
-/
theorem _root_.GlobalTheory.T.dual_class_twist_neg : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL k) (s : ℂ), dualCl (x.nu s) = (dualCl x).nu (-s) := by
  first | exact @GlobalTheory.CompanionTheory.ZcDual.dualCl_nu | exact GlobalTheory.CompanionTheory.ZcDual.dualCl_nu | (intros; apply GlobalTheory.CompanionTheory.ZcDual.dualCl_nu <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsFactorsDualReverseOrdered
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.DualForms.exists_revOrdered_dual` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLanglandsFactorsDualReverseOrdered.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.langlands_factors_dual_reverse_ordered : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegDual k → ∀ (𝔪 : Multiset (Segment k)) {h : ℕ} (x : Fin h → IrrGL k), LFactors 𝔪 x → ∃ Γ : Fin h → Segment k, IsRevOrdered Γ ∧ ∀ i, IsLSeg (Γ i) (dualCl (x i)).rep := by
  first | exact @GlobalTheory.CompanionTheory.DualForms.exists_revOrdered_dual | exact GlobalTheory.CompanionTheory.DualForms.exists_revOrdered_dual | (intros; apply GlobalTheory.CompanionTheory.DualForms.exists_revOrdered_dual <;> assumption)

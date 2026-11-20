import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFree
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LSocle.lSocleGL` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLanglandsSocleOfOrderFree.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.langlands_socle_of_order_free : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GKLocal k → LOrderFree k → LSocleGL k := by
  first | exact @GlobalTheory.CompanionTheory.LSocle.lSocleGL | exact GlobalTheory.CompanionTheory.LSocle.lSocleGL | (intros; apply GlobalTheory.CompanionTheory.LSocle.lSocleGL <;> assumption)

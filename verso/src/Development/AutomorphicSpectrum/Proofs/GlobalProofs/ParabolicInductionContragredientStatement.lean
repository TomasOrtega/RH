import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionContragredient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Glob.inductionContragredient` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FParabolicInductionContragredient.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.parabolic_induction_contragredient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.InductionContragredient k := by
  first | exact @GlobalTheory.CompanionTheory.Glob.inductionContragredient | exact GlobalTheory.CompanionTheory.Glob.inductionContragredient | (intros; apply GlobalTheory.CompanionTheory.Glob.inductionContragredient <;> assumption)

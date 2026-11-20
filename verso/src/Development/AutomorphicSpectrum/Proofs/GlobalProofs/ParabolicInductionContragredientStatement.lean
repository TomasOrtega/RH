import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionContragredient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.Glob.inductionContragredient | exact GlobalTheory.CompanionTheory.Glob.inductionContragredient | (intros; apply GlobalTheory.CompanionTheory.Glob.inductionContragredient <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.parabolic_induction_contragredient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.InductionContragredient k := by
  first | exact @GlobalTheory.CompanionTheory.Glob.inductionContragredient | exact GlobalTheory.CompanionTheory.Glob.inductionContragredient | (intros; apply GlobalTheory.CompanionTheory.Glob.inductionContragredient <;> assumption)

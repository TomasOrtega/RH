import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FParabolicInductionFiniteLength.lean&line=247#L247)
-/
theorem _root_.GlobalTheory.T.parabolic_induction_finite_length : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.InductionFiniteLength k := by
  first | exact @GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength | exact GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength | (intros; apply GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength <;> assumption)

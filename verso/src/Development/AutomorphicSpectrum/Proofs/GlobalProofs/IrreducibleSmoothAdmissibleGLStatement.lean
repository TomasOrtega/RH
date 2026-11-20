import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IrreducibleSmoothAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FIrreducibleSmoothAdmissibleGL.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.irreducible_smooth_admissible_GL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.IrreducibleAdmissible k := by
  first | exact @GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible | exact GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible | (intros; apply GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible <;> assumption)

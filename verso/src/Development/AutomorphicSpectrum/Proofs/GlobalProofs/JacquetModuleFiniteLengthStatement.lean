import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FJacquetModuleFiniteLength.lean&line=100#L100)
-/
theorem _root_.GlobalTheory.T.jacquet_module_finite_length : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetFiniteLength k := by
  first | exact @GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength | exact GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength | (intros; apply GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength <;> assumption)

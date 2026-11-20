import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsRealFlowAdelicUnits
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SW.Flow.exists_flow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FExistsRealFlowAdelicUnits.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.exists_real_flow_adelic_units : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ := by
  first | exact @GlobalTheory.CompanionTheory.SW.Flow.exists_flow | exact GlobalTheory.CompanionTheory.SW.Flow.exists_flow | (intros; apply GlobalTheory.CompanionTheory.SW.Flow.exists_flow <;> assumption)

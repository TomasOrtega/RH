import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContDiffOnChartGlobalWhittakerCoefficient
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SW.LatCpt.latV_compact_open` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FContDiffOnChartGlobalWhittakerCoefficient.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.contDiffOn_chart_globalWhittakerCoefficient : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (v : HeightOneSpectrum (𝓞 F)), IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) ∧ IsOpen (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.LatCpt.latV_compact_open | exact GlobalTheory.CompanionTheory.SW.LatCpt.latV_compact_open | (intros; apply GlobalTheory.CompanionTheory.SW.LatCpt.latV_compact_open <;> assumption)

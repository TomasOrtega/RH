import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitsDecompositionFlowCompact
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SW.Fujisaki.units_decomp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FAdelicUnitsDecompositionFlowCompact.lean&line=180#L180)
-/
theorem _root_.GlobalTheory.T.adelic_units_decomposition_flow_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∃ ω : Set (AF F ⊗[F] E)ˣ, IsCompact ω ∧ ∀ a : (AF F ⊗[F] E)ˣ, ∃ (l : Eˣ) (a' : (AF F ⊗[F] E)ˣ) (c : (AF F ⊗[F] E)ˣ) (j : ℤ), (a' : AF F ⊗[F] E) = inclR (AF F) (l : E) ∧ c ∈ ω ∧ a = a' * τ (Multiplicative.ofAdd (j : ℝ)) * c := by
  first | exact @GlobalTheory.CompanionTheory.SW.Fujisaki.units_decomp | exact GlobalTheory.CompanionTheory.SW.Fujisaki.units_decomp | (intros; apply GlobalTheory.CompanionTheory.SW.Fujisaki.units_decomp <;> assumption)

import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainExistsUnitary
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SW.haar_fundamental_exist` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FHaarFundamentalDomainExistsUnitary.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.haar_fundamental_domain_exists_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∃ μ, IsHaarH F E σ M J μ) ∧ ∀ μ, IsHaarH F E σ M J μ → (∃ 𝓕, IsFDH F E σ M J μ 𝓕) ∧ (∃ 𝓕, MeasurableSet 𝓕 ∧ IsFDH F E σ M J μ 𝓕 ∧ ∀ h : HA (AF F) σ J, ∃ γ : HA (AF F) σ J, HA.mat (AF F) σ J γ ∈ HFin (AF F) σ J ∧ γ * h ∈ 𝓕) ∧ ∀ 𝓕, IsFDH F E σ M J μ 𝓕 → μ 𝓕 ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.haar_fundamental_exist | exact GlobalTheory.CompanionTheory.SW.haar_fundamental_exist | (intros; apply GlobalTheory.CompanionTheory.SW.haar_fundamental_exist <;> assumption)

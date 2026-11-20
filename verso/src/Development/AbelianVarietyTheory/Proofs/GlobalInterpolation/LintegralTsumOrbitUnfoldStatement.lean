import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LintegralTsumOrbitUnfold
import Mathlib
open MeasureTheory Topology
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.lintegral_tsum_orbit_unfold` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FLintegralTsumOrbitUnfold.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.lintegral_tsum_orbit_unfold_alt : ∀ (G G' V X : Type) [Group G] [Group G'] [MeasurableSpace G] [MeasurableSpace G'] [MeasurableMul₂ G] [MeasurableInv G] [MeasurableMul G'] [MulAction G V] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (μ' : Measure G') [SFinite μ'] [μ'.IsMulLeftInvariant] (Γ : Subgroup G) (Γ' : Subgroup G') [Countable Γ] [Countable Γ'] (𝓕 : Set G) (𝓕' : Set G'), IsFundamentalDomain Γ 𝓕 μ → IsFundamentalDomain Γ' 𝓕' μ' → ∀ (φ : G' →* G), Measurable φ → Function.Injective φ → (∀ g, φ g ∈ Γ ↔ g ∈ Γ') → ∀ (x : V), φ.range = MulAction.stabilizer G x → ∀ (c : X → V), Function.Injective c → (∀ y, y ∈ Set.range c ↔ ∃ γ ∈ Γ, γ • x = y) → ∀ (u : G → ℝ≥0∞), Measurable u → ∀ (Φ : V → ℝ≥0∞), (∀ h : G, Φ (h⁻¹ • x) = ∫⁻ g, u ((φ g)⁻¹ * h) ∂μ') → ∫⁻ h in 𝓕, ∑' i, Φ (h⁻¹ • c i) ∂μ = μ' 𝓕' * ∫⁻ h, u h ∂μ := by
  first | exact @GlobalTheory.lintegral_tsum_orbit_unfold | exact GlobalTheory.lintegral_tsum_orbit_unfold | (intros; apply GlobalTheory.lintegral_tsum_orbit_unfold <;> assumption)

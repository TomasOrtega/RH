import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedAverageApproxOfSubgroupFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyIntegrableRep
open MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_average_fixed_approx_of_fixed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFixedAverageApproxOfSubgroupFixed.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exists_fixed_average_approx_of_subgroup_fixed : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K], ∀ (ρ : G →* (K →L[ℂ] K)), (∀ g v, ‖ρ g v‖ = ‖v‖) → (∀ v, Continuous fun g => ρ g v) → ∀ (H U : Subgroup G), IsOpen (U : Set G) → (∀ y ∈ U, ∀ k ∈ H, y⁻¹ * k * y ∈ H) → ∀ v : K, (∀ k ∈ H, ρ k v = v) → ∀ ε : ℝ, 0 < ε → ∃ η : G → ℂ, Continuous η ∧ HasCompactSupport η ∧ (∀ k ∈ H, ρ k (∫ y, η y • ρ y v ∂μ) = ∫ y, η y • ρ y v ∂μ) ∧ ‖v - ∫ y, η y • ρ y v ∂μ‖ < ε := by
  first | exact @GlobalTheory.exists_average_fixed_approx_of_fixed | exact GlobalTheory.exists_average_fixed_approx_of_fixed | (intros; apply GlobalTheory.exists_average_fixed_approx_of_fixed <;> assumption)

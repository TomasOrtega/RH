import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMeasureByInvariantSubgroup
import Mathlib
open MeasureTheory Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Shear.lintegral_shear_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FQuotientMeasureByInvariantSubgroup.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.quotient_measure_by_invariant_subgroup : ∀ (V A : Type) [AddCommGroup V] [AddCommGroup A] [MeasurableSpace V] [MeasurableSpace A] [MeasurableAdd₂ V] [MeasurableAdd₂ A] [MeasurableNeg A] [MeasurableNeg V] (μ : Measure V) (lam : Measure A) [SFinite μ] [SFinite lam] [μ.IsAddRightInvariant] [lam.IsAddRightInvariant] (j : A →+ V), Measurable j → ∀ f : V → A, Measurable f → (∀ v a, f (v + j a) = f v) → ∀ K : Set A, MeasurableSet K → lam K ≠ 0 → lam K ≠ ⊤ → ∀ ψ : V → ℝ≥0∞, Measurable ψ → ∫⁻ v, ψ (v + j (f v)) ∂μ = ∫⁻ v, ψ v ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.Shear.lintegral_shear_eq | exact GlobalTheory.CompanionTheory.Shear.lintegral_shear_eq | (intros; apply GlobalTheory.CompanionTheory.Shear.lintegral_shear_eq <;> assumption)

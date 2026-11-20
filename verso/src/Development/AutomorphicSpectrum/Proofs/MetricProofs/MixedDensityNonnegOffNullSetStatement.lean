import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet
import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Giv.mInt_eq_integral_maMeasure_off_null` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FMixedDensityNonnegOffNullSet.lean&line=294#L294)
-/
theorem _root_.GlobalTheory.T.mInt_eq_integral_maMeasure : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (U : Set X) (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (Θ : LocPot X), IsOpen U → (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Uᶜ) = 0) → (∀ i, IsPotential A (P i)) → IsPotential A Θ → IsPsh A Θ → (∀ i, A.SmoothOn U (f i)) → (∀ i, IsPshOn A U (P i + LocPot.ofFun (f i) + Θ)) → ∀ g : X → ℝ, ContinuousOn g U → Integrable g (maMeasure A fun i => P i + LocPot.ofFun (f i) + Θ) → MIntegrable A (fun i => P i + LocPot.ofFun (f i) + Θ) g ∧ mInt A (fun i => P i + LocPot.ofFun (f i) + Θ) g = ∫ y, g y ∂(maMeasure A fun i => P i + LocPot.ofFun (f i) + Θ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.mInt_eq_integral_maMeasure_off_null | exact GlobalTheory.CompanionTheory.Ar.Giv.mInt_eq_integral_maMeasure_off_null | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.mInt_eq_integral_maMeasure_off_null <;> assumption)

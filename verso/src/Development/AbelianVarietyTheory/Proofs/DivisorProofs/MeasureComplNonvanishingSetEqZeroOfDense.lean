import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

/- English proof (translation)
Introduce `n Y _ _ _ _ _ ι La _ A Λ τ hτ hd`. Establish `hN : EXTNullStatement n` using `extNull n`. Establish `hiff : ∀ i y, y ∈ (A.chart i).source → (τ (A.pick y) y ≠ 0 ↔ τ i y ≠ 0)`. Introduce `i y hy`. Rewrite using `[hτ.2 (A.pick y) i y trivial (A.mem_pick y) hy]`.

Simplify using `[A.g_ne Λ (A.pick y) i y (A.mem_pick y) hy]`. Use `measure_null_of_locally_null _ fun y _ => ?_` and prove the remaining obligations. Establish `hys : y ∈ (A.chart (A.pick y)).source` using `A.mem_pick y`. Establish `hv` using `(A.chart (A.pick y)).map_source hys`. Take `⟨r, hr, hB⟩` from `Metric.isOpen_iff.1 (A.chart (A.pick y)).open_target _ hv`.

Establish `hUo : IsOpen ((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹' Metric.ball (A.chart (A.pick y) y) r)` using `(A.chart _).continuousOn.isOpen_inter_preimage (A.chart _).open_source Metric.isOpen_ball`. Establish `hyU : y ∈ (A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹' Metric.ball (A.chart (A.pick y) y) r` using `⟨hys, Metric.mem_ball_self hr⟩`. Establish `hF : DifferentiableOn ℂ (τ (A.pick y) ∘ (A.chart (A.pick y)).symm) (A.chart (A.pick y)).target`. Simplify using `using hτ.1 (A.pick y)`. Establish `hcont : ContinuousOn (τ (A.pick y)) (A.chart (A.pick y)).source`.

Use `hF.continuousOn.comp (A.chart (A.pick y)).continuousOn (fun x hx => (A.chart (A.pick y)).map_source hx)` as an intermediate fact. Use `this.congr fun x hx => ?_` and prove the remaining obligations. Simplify using `[Function.comp, (A.chart (A.pick y)).left_inv hx]`. Establish `hTo : IsOpen (((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹' Metric.ball (A.chart (A.pick y) y) r) ∩ τ (A.pick y) ⁻¹' {0}ᶜ)` using `(hcont.mono Set.inter_subset_left).isOpen_inter_preimage hUo isOpen_compl_singleton`. Use `⟨_, inter_mem_nhdsWithin _ (hUo.mem_nhds hyU), ?_⟩` and prove the remaining obligations.

Use `measure_mono_null (t := ((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹' Metric.ball (A.chart (A.pick y) y) r) \ (((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹' Metric.ball (A.chart (A.pick y) y) r) ∩ τ (A.pick y) ⁻¹' {0}ᶜ)) ?_ ?_` and prove the remaining obligations. Introduce and unpack `x ⟨hxn, hxU⟩`. Use `⟨hxU, fun h => hxn ?_⟩` and prove the remaining obligations. Conclude with `(hiff _ x hxU.1).2 h.2`. Rewrite using `[A.mu_chart (A.pick y) _ (hUo.measurableSet.diff hTo.measurableSet) (Set.diff_subset.trans Set.inter_subset_left)]`.

Apply `setLIntegral_measure_zero` to reduce the goal to its premises. Take `⟨y', hy'U, hy'M⟩` from `hd.inter_open_nonempty _ hUo ⟨y, hyU⟩`. Establish `hnull` using `hN (A.chart (A.pick y) y) r (τ (A.pick y) ∘ (A.chart (A.pick y)).symm) (hF.mono hB) ⟨A.chart (A.pick y) y', hy'U.2, by`. Simplify using `only [Function.comp, (A.chart _).left_inv hy'U.1]`. Conclude with `(hiff _ y' hy'U.1).1 hy'M⟩`.

Use `measure_mono_null ?_ hnull` and prove the remaining obligations. Introduce and unpack `_ ⟨x, ⟨hxU, hxn⟩, rfl⟩`. Use `⟨hxU.2, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, Function.comp, (A.chart _).left_inv hxU.1]`. Assume the negation of the conclusion as `h`.

Conclude with `hxn ⟨hxU, h⟩`.
-/
theorem zeroSet_null_of_dense_nz : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ), A.IsSec Λ τ → Dense (nz A τ) → A.mu (nz A τ)ᶜ = 0 := by
  intro n Y _ _ _ _ _ ι La _ A Λ τ hτ hd
  have hN : EXTNullStatement n := extNull n
  have hiff : ∀ i y, y ∈ (A.chart i).source → (τ (A.pick y) y ≠ 0 ↔ τ i y ≠ 0) := by
    intro i y hy
    rw [hτ.2 (A.pick y) i y trivial (A.mem_pick y) hy]
    simp [A.g_ne Λ (A.pick y) i y (A.mem_pick y) hy]
  refine measure_null_of_locally_null _ fun y _ => ?_
  have hys : y ∈ (A.chart (A.pick y)).source := A.mem_pick y
  have hv := (A.chart (A.pick y)).map_source hys
  obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.1 (A.chart (A.pick y)).open_target _ hv
  have hUo : IsOpen ((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
      Metric.ball (A.chart (A.pick y) y) r) :=
    (A.chart _).continuousOn.isOpen_inter_preimage (A.chart _).open_source Metric.isOpen_ball
  have hyU : y ∈ (A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
      Metric.ball (A.chart (A.pick y) y) r := ⟨hys, Metric.mem_ball_self hr⟩
  have hF : DifferentiableOn ℂ (τ (A.pick y) ∘ (A.chart (A.pick y)).symm)
      (A.chart (A.pick y)).target := by
    simpa using hτ.1 (A.pick y)
  have hcont : ContinuousOn (τ (A.pick y)) (A.chart (A.pick y)).source := by
    have := hF.continuousOn.comp (A.chart (A.pick y)).continuousOn
      (fun x hx => (A.chart (A.pick y)).map_source hx)
    refine this.congr fun x hx => ?_
    simp [Function.comp, (A.chart (A.pick y)).left_inv hx]
  have hTo : IsOpen (((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
      Metric.ball (A.chart (A.pick y) y) r) ∩ τ (A.pick y) ⁻¹' {0}ᶜ) :=
    (hcont.mono Set.inter_subset_left).isOpen_inter_preimage hUo isOpen_compl_singleton
  refine ⟨_, inter_mem_nhdsWithin _ (hUo.mem_nhds hyU), ?_⟩
  refine measure_mono_null (t := ((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
      Metric.ball (A.chart (A.pick y) y) r) \ (((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
      Metric.ball (A.chart (A.pick y) y) r) ∩ τ (A.pick y) ⁻¹' {0}ᶜ)) ?_ ?_
  · rintro x ⟨hxn, hxU⟩
    refine ⟨hxU, fun h => hxn ?_⟩
    exact (hiff _ x hxU.1).2 h.2
  rw [A.mu_chart (A.pick y) _ (hUo.measurableSet.diff hTo.measurableSet)
    (Set.diff_subset.trans Set.inter_subset_left)]
  apply setLIntegral_measure_zero
  obtain ⟨y', hy'U, hy'M⟩ := hd.inter_open_nonempty _ hUo ⟨y, hyU⟩
  have hnull := hN (A.chart (A.pick y) y) r (τ (A.pick y) ∘ (A.chart (A.pick y)).symm)
    (hF.mono hB) ⟨A.chart (A.pick y) y', hy'U.2, by
      simp only [Function.comp, (A.chart _).left_inv hy'U.1]
      exact (hiff _ y' hy'U.1).1 hy'M⟩
  refine measure_mono_null ?_ hnull
  rintro _ ⟨x, ⟨hxU, hxn⟩, rfl⟩
  refine ⟨hxU.2, ?_⟩
  simp only [Set.mem_setOf_eq, Function.comp, (A.chart _).left_inv hxU.1]
  by_contra h
  exact hxn ⟨hxU, h⟩

end GlobalTheory

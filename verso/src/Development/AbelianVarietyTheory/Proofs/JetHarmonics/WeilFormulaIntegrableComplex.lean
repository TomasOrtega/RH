import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

/- English proof (translation)
Establish `hmx : ∀ x, Measurable (fun s => m s x)` using `fun x => hm.comp (measurable_id.prodMk measurable_const)`. Set `η : ProbabilityTheory.Kernel X Y` to `{ toFun := fun x => σ.map (fun s => m s x) measurable' := by`. Use `Measure.measurable_of_measurable_coe _ (fun A hA => ?_)` and prove the remaining obligations. Repeatedly rewrite using `[Measure.map_apply (hmx _) hA]`. Conclude with `measurable_measure_prodMk_right (hm hA) }`.

Establish `hη : ∀ x, η x = σ.map (fun s => m s x)` using `fun _ => rfl`. Establish `hμ : (ProbabilityTheory.Kernel.comp η (ProbabilityTheory.Kernel.const Unit ν)) () = μ`. Use extensionality with `A hA`. Rewrite using `[ProbabilityTheory.Kernel.comp_apply' _ _ _ hA, ProbabilityTheory.Kernel.const_apply, ← lintegral_indicator_one hA, hq _ (measurable_one.indicator hA)]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations.

Rewrite using `[hη, ← lintegral_indicator_one hA, lintegral_map (measurable_one.indicator hA) (hmx x)]`. Establish `hI : ∀ x, ∫ y, f y ∂η x = ∫ s, f (m s x) ∂σ` using `fun x => by`. Rewrite using `[hη, integral_map (hmx x).aemeasurable hf.aestronglyMeasurable]`. Rewrite `hi` using `[← hμ]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `h` using `hi.ae_of_comp`. Rewrite `h` using `[ProbabilityTheory.Kernel.const_apply]`. Use `filter_upwards [h] with x hx`. Rewrite `hx` using `[hη]`. Conclude with `(integrable_map_measure hf.aestronglyMeasurable (hmx x).aemeasurable).1 hx`.

Establish `h` using `hi.integral_comp`. Rewrite `h` using `[ProbabilityTheory.Kernel.const_apply]`. Simplify `h` using `only [hI]`. Establish `h` using `ProbabilityTheory.Kernel.integral_comp hi`. Rewrite `h` using `[ProbabilityTheory.Kernel.const_apply, hμ]`.

Simplify `h` using `only [hI]`.
-/
theorem unfold_integral_of_lintegral {S X Y E : Type*} [MeasurableSpace S] [MeasurableSpace X]
    [MeasurableSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Y) (σ : Measure S) (ν : Measure X) [SFinite σ] (m : S → X → Y)
    (hm : Measurable (fun q : S × X => m q.1 q.2))
    (hq : ∀ g : Y → ℝ≥0∞, Measurable g → ∫⁻ y, g y ∂μ = ∫⁻ x, ∫⁻ s, g (m s x) ∂σ ∂ν)
    (f : Y → E) (hf : StronglyMeasurable f) (hi : Integrable f μ) :
    (∀ᵐ x ∂ν, Integrable (fun s => f (m s x)) σ) ∧ Integrable (fun x => ∫ s, f (m s x) ∂σ) ν ∧
      ∫ y, f y ∂μ = ∫ x, (∫ s, f (m s x) ∂σ) ∂ν := by
  have hmx : ∀ x, Measurable (fun s => m s x) := fun x =>
    hm.comp (measurable_id.prodMk measurable_const)
  let η : ProbabilityTheory.Kernel X Y :=
    { toFun := fun x => σ.map (fun s => m s x)
      measurable' := by
        refine Measure.measurable_of_measurable_coe _ (fun A hA => ?_)
        simp_rw [Measure.map_apply (hmx _) hA]
        exact measurable_measure_prodMk_right (hm hA) }
  have hη : ∀ x, η x = σ.map (fun s => m s x) := fun _ => rfl
  have hμ : (ProbabilityTheory.Kernel.comp η (ProbabilityTheory.Kernel.const Unit ν)) () = μ := by
    ext A hA
    rw [ProbabilityTheory.Kernel.comp_apply' _ _ _ hA, ProbabilityTheory.Kernel.const_apply,
      ← lintegral_indicator_one hA, hq _ (measurable_one.indicator hA)]
    refine lintegral_congr fun x => ?_
    rw [hη, ← lintegral_indicator_one hA, lintegral_map (measurable_one.indicator hA) (hmx x)]
  have hI : ∀ x, ∫ y, f y ∂η x = ∫ s, f (m s x) ∂σ := fun x => by
    rw [hη, integral_map (hmx x).aemeasurable hf.aestronglyMeasurable]
  rw [← hμ] at hi
  refine ⟨?_, ?_, ?_⟩
  · have h := hi.ae_of_comp
    rw [ProbabilityTheory.Kernel.const_apply] at h
    filter_upwards [h] with x hx
    rw [hη] at hx
    exact (integrable_map_measure hf.aestronglyMeasurable (hmx x).aemeasurable).1 hx
  · have h := hi.integral_comp
    rw [ProbabilityTheory.Kernel.const_apply] at h
    simpa only [hI] using h
  · have h := ProbabilityTheory.Kernel.integral_comp hi
    rw [ProbabilityTheory.Kernel.const_apply, hμ] at h
    simpa only [hI] using h

/- English proof (translation)
Introduce `k r μG μS νq _ f hq hf hi`. Establish `hc : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of q.1 * Matrix.of q.2) i j : Formalism.QuantumDeterminants.Mt k r))`. Establish `h1 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of q.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))` using `continuous_fst`. Establish `h2 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of q.2 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))` using `continuous_snd`. Conclude with `h1.matrix_mul h2`.

Conclude with `unfold_integral_of_lintegral μG μS νq (fun s x => (fun i j => (Matrix.of s * Matrix.of x) i j : Formalism.QuantumDeterminants.Mt k r)) hc.measurable hq f hf.stronglyMeasurable hi`.
-/
theorem weil_formula_integrable : ∀ (k r : ℕ) (μG μS νq : Measure (Formalism.QuantumDeterminants.Mt k r)) [SFinite μS] (f : Formalism.QuantumDeterminants.Mt k r → ℂ), PI.BesselPeriodGGP.IsQuotMeas μG μS νq → Measurable f → Integrable f μG → (∀ᵐ x ∂νq, Integrable (fun s => f (fun i j => (Matrix.of s * Matrix.of x) i j)) μS) ∧ Integrable (fun x => ∫ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) νq ∧ ∫ x, f x ∂μG = ∫ x, (∫ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂νq := by
  intro k r μG μS νq _ f hq hf hi
  have hc : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of q.1 * Matrix.of q.2) i j : Formalism.QuantumDeterminants.Mt k r)) := by
    have h1 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (Matrix.of q.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) := continuous_fst
    have h2 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (Matrix.of q.2 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) := continuous_snd
    exact h1.matrix_mul h2
  exact unfold_integral_of_lintegral μG μS νq
    (fun s x => (fun i j => (Matrix.of s * Matrix.of x) i j : Formalism.QuantumDeterminants.Mt k r))
    hc.measurable hq f hf.stronglyMeasurable hi

end GlobalTheory

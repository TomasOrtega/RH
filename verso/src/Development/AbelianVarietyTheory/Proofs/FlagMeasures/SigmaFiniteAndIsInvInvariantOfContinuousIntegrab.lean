import Mathlib

open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Introduce `G _ _ _ _ _ _ μ _ _ f hfc hf1 hfi`. Establish `hf1' : ‖f 1‖ₑ ≠ 0` using `enorm_ne_zero.2 hf1`. Establish `hc0 : ‖f 1‖ₑ / 2 ≠ 0` using `by simp [hf1']`. Establish `hcT : ‖f 1‖ₑ / 2 ≠ ⊤` using `(ENNReal.div_lt_top enorm_ne_top two_ne_zero).ne`. Establish `hUo : IsOpen {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}` using `isOpen_lt continuous_const hfc.enorm`.

Establish `h1U : (1 : G) ∈ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}` using `ENNReal.half_lt_self hf1' enorm_ne_top`. Establish `hUfin : μ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} < ⊤`. Combine the equalities or inequalities in the displayed calculation. Establish `hσ : SigmaFinite μ`. Take `⟨T, hTc, hT⟩` from `TopologicalSpace.isOpen_iUnion_countable (fun g : G => (fun y => g⁻¹ * y) ⁻¹' {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}) (fun g => hUo.preimage (continuous_const.mul continuous_id))`.

Use `Measure.sigmaFinite_of_countable (hTc.image fun g : G => (fun y => g⁻¹ * y) ⁻¹' {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}) ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, -, rfl⟩`. Rewrite using `[measure_preimage_mul]`. Conclude with `hUfin`. Rewrite using `[Set.sUnion_image, hT]`.

Use `Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, ?_⟩` and prove the remaining obligations. Use `show x⁻¹ * x ∈ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}`. Rewrite using `[inv_mul_cancel]`. Conclude with `h1U`. Establish `key : μ.inv = μ` using `by open Pointwise in`.

Establish `hVo : IsOpen ({x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ∩ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}⁻¹)` using `hUo.inter hUo.inv`. Use `open Pointwise in`. Establish `hV0 : μ ({x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ∩ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}⁻¹) ≠ 0` using `(hVo.measure_pos μ ⟨1, h1U, by simpa using h1U⟩).ne'`. Use `open Pointwise in`. Establish `hVT : μ ({x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ∩ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}⁻¹) ≠ ⊤` using `((measure_mono Set.inter_subset_left).trans_lt hUfin).ne`.

Use `open Pointwise in`. Establish `hVinv : μ.inv ({x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ∩ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}⁻¹) = μ ({x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ∩ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}⁻¹)`. Rewrite using `[Measure.inv_apply, Set.inter_inv, inv_inv, Set.inter_comm]`. Rewrite using `[measure_eq_div_smul μ.inv μ hV0 hVT, hVinv, ENNReal.div_self hV0 hVT, one_smul]`. Conclude with `⟨hσ, ⟨key⟩⟩`.
-/
theorem sigmaFinite_and_isInvInvariant_of_continuous_integrable :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
      [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : G → ℂ),
      Continuous f → f 1 ≠ 0 → Integrable f μ → SigmaFinite μ ∧ μ.IsInvInvariant := by
  intro G _ _ _ _ _ _ μ _ _ f hfc hf1 hfi

  have hf1' : ‖f 1‖ₑ ≠ 0 := enorm_ne_zero.2 hf1
  have hc0 : ‖f 1‖ₑ / 2 ≠ 0 := by simp [hf1']
  have hcT : ‖f 1‖ₑ / 2 ≠ ⊤ := (ENNReal.div_lt_top enorm_ne_top two_ne_zero).ne

  have hUo : IsOpen {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} := isOpen_lt continuous_const hfc.enorm
  have h1U : (1 : G) ∈ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} :=
    ENNReal.half_lt_self hf1' enorm_ne_top

  have hUfin : μ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} < ⊤ := by
    calc μ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ≤ μ {x : G | ‖f 1‖ₑ / 2 ≤ ‖f x‖ₑ} :=
          measure_mono (Set.setOf_subset_setOf.2 fun _ hx => hx.le)
      _ ≤ (∫⁻ x, ‖f x‖ₑ ∂μ) / (‖f 1‖ₑ / 2) :=
          meas_ge_le_lintegral_div hfi.aestronglyMeasurable.enorm hc0 hcT
      _ < ⊤ := ENNReal.div_lt_top hfi.2.ne hc0

  have hσ : SigmaFinite μ := by
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun g : G => (fun y => g⁻¹ * y) ⁻¹' {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ})
      (fun g => hUo.preimage (continuous_const.mul continuous_id))
    refine Measure.sigmaFinite_of_countable
      (hTc.image fun g : G => (fun y => g⁻¹ * y) ⁻¹' {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}) ?_ ?_
    · rintro _ ⟨g, -, rfl⟩
      rw [measure_preimage_mul]
      exact hUfin
    · rw [Set.sUnion_image, hT]
      refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, ?_⟩
      show x⁻¹ * x ∈ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}
      rw [inv_mul_cancel]
      exact h1U

  have key : μ.inv = μ := by
    open Pointwise in
    have hVo : IsOpen ({x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ∩ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}⁻¹) := hUo.inter hUo.inv
    open Pointwise in
    have hV0 : μ ({x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ∩ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}⁻¹) ≠ 0 :=
      (hVo.measure_pos μ ⟨1, h1U, by simpa using h1U⟩).ne'
    open Pointwise in
    have hVT : μ ({x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ∩ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}⁻¹) ≠ ⊤ :=
      ((measure_mono Set.inter_subset_left).trans_lt hUfin).ne
    open Pointwise in
    have hVinv : μ.inv ({x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ∩ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}⁻¹) = μ ({x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ∩ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}⁻¹) := by
      rw [Measure.inv_apply, Set.inter_inv, inv_inv, Set.inter_comm]
    rw [measure_eq_div_smul μ.inv μ hV0 hVT, hVinv, ENNReal.div_self hV0 hVT, one_smul]
  exact ⟨hσ, ⟨key⟩⟩

end GlobalTheory

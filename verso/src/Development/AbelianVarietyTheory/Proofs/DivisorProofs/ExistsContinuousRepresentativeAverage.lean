import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyIntegrableRep
open MeasureTheory
open scoped ContDiff

namespace GlobalTheory.LocRep

open MeasureTheory in
open scoped ContDiff Pointwise in

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ μ _ K _ _ _ ι hloc hlin ρ hnorm hcont htrans η v hηc hηs`. Establish `hιv : LocallyIntegrable (ι v) μ` using `_root_.GlobalTheory.LocRep.locallyIntegrable_rep hloc v`. Take `⟨B, hB⟩` from `hηc.bounded_above_of_compact_support hηs`. Use `set φ : G → ℂ := fun x => ∫ y, η y * ι v (x * y) ∂μ with hφdef`. Establish `hφeq : φ = fun x => ∫ z, η (x⁻¹ * z) * ι v z ∂μ`.

Use function extensionality and compare the values at `x`. Rewrite using `[hφdef, ← integral_mul_left_eq_self (fun z => η (x⁻¹ * z) * ι v z) x]`. Simplify using the standard rewrite rules. Establish `hφc : Continuous φ`. Rewrite using `[hφeq, continuous_iff_continuousAt]`.

Introduce `x₀`. Take `⟨V, hV, hVn⟩` from `exists_compact_mem_nhds x₀`. Establish `hL : IsCompact (V * tsupport η)` using `hV.mul hηs`. Use `continuousAt_of_dominated (bound := (V * tsupport η).indicator fun z => B * ‖ι v z‖) (Filter.Eventually.of_forall fun x => ((hηc.comp (continuous_const.mul continuous_id)).aestronglyMeasurable).mul hιv.aestronglyMeasurable) ?_ ?_ (Filter.Eventually.of_forall fun z => ((hηc.comp ( …` and prove the remaining obligations. Use `filter_upwards [hVn] with x hx`.

Use `Filter.Eventually.of_forall fun z => ?_` and prove the remaining obligations. Distinguish the cases in `hz : η (x⁻¹ * z) = 0`. Rewrite using `[hz, zero_mul, norm_zero]`. Conclude with `Set.indicator_nonneg (fun _ _ => mul_nonneg ((norm_nonneg _).trans (hB 1)) (norm_nonneg _)) _`. Establish `hzL : z ∈ V * tsupport η`.

Use `Set.mul_mem_mul hx (subset_tsupport η hz)` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`. Then use the resulting hypothesis. Rewrite using `[Set.indicator_of_mem hzL, norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)`. Conclude with `IntegrableOn.integrable_indicator ((hιv.integrableOn_isCompact hL).norm.const_mul B) hL.measurableSet`.

Use `⟨φ, hφc, _root_.GlobalTheory.LocRep.rep_of_pairing hloc hφc.locallyIntegrable ?_⟩` and prove the remaining obligations. Introduce `C hC`. Take `⟨Λ, hΛ⟩` from `_root_.GlobalTheory.LocRep.exists_pairing hloc hlin hC`. Take `⟨M, hM⟩` from `hloc C hC`. Establish `hint : Integrable (fun y => η y • ρ y v) μ` using `(hηc.smul (hcont v)).integrable_of_hasCompactSupport hηs.smul_right`.

Establish `hηI : Integrable η μ` using `hηc.integrable_of_hasCompactSupport hηs`. Establish `hrestr : μ.prod (μ.restrict C) = (μ.prod μ).restrict (Set.univ ×ˢ C)`. Rewrite using `[← Measure.prod_restrict, Measure.restrict_univ]`. Establish `hmeas : AEStronglyMeasurable (fun p : G × G => η p.1 * ι v (p.2 * p.1)) (μ.prod (μ.restrict C))`. Establish `h1 : AEStronglyMeasurable (fun p : G × G => ι v (p.2 * p.1)) (μ.prod μ)` using `(hιv.aestronglyMeasurable.comp_snd (μ := μ)).comp_measurePreserving (measurePreserving_prod_mul_swap μ μ)`.

Rewrite using `[hrestr]`. Conclude with `((hηc.comp continuous_fst).aestronglyMeasurable).mul h1.restrict`. Establish `hslice : ∀ y, IntegrableOn (fun x => ι v (x * y)) C μ ∧ ∫ x in C, ‖ι v (x * y)‖ ∂μ ≤ M * ‖v‖`. Introduce `y`. Establish `hae : ι (ρ y v) =ᵐ[μ.restrict C] fun x => ι v (x * y)` using `ae_restrict_of_ae (htrans y v)`.

Take `⟨h1, h2⟩` from `hM (ρ y v)`. Use `⟨h1.congr_fun_ae hae, ?_⟩` and prove the remaining obligations. Rewrite using `[← hnorm y v]`. Use `le_of_eq_of_le (integral_congr_ae (hae.mono fun x hx => ?_)).symm h2` and prove the remaining obligations. Simplify using `only [hx]`.

Establish `hprod : Integrable (Function.uncurry fun y x => η y * ι v (x * y)) (μ.prod (μ.restrict C))`. Use `(integrable_prod_iff hmeas).2 ⟨Filter.Eventually.of_forall fun y => (hslice y).1.const_mul (η y), ?_⟩` and prove the remaining obligations. Use `Integrable.mono' (hηI.norm.mul_const (M * ‖v‖)) hmeas.norm.integral_prod_right' ?_` and prove the remaining obligations. Use `Filter.Eventually.of_forall fun y => ?_` and prove the remaining obligations. Simplify using `only [norm_mul, Function.uncurry_apply_pair]`.

Rewrite using `[Real.norm_of_nonneg (integral_nonneg fun _ => by positivity), integral_const_mul]`. Conclude with `mul_le_mul_of_nonneg_left (hslice y).2 (norm_nonneg _)`. Combine the equalities or inequalities in the displayed calculation. Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[map_smul, hΛ, smul_eq_mul, ← integral_const_mul]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_restrict_of_ae (htrans y v)] with x hx`. Rewrite using `[hx]`. Use `_ = ∫ x in C, φ x ∂μ := integral_integral_swap hprod`.
-/
theorem _root_.GlobalTheory.LocRep.exists_continuous_rep_average : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ι : K → G → ℂ), (∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖) → (∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) → ∀ (ρ : G →* (K →L[ℂ] K)), (∀ g v, ‖ρ g v‖ = ‖v‖) → (∀ v, Continuous fun g => ρ g v) → (∀ g v, ι (ρ g v) =ᵐ[μ] fun x => ι v (x * g)) → ∀ (η : G → ℂ) (v : K), Continuous η → HasCompactSupport η → ∃ φ : G → ℂ, Continuous φ ∧ ι (∫ y, η y • ρ y v ∂μ) =ᵐ[μ] φ := by
  intro G _ _ _ _ _ _ _ _ μ _ K _ _ _ ι hloc hlin ρ hnorm hcont htrans η v hηc hηs
  have hιv : LocallyIntegrable (ι v) μ := _root_.GlobalTheory.LocRep.locallyIntegrable_rep hloc v
  obtain ⟨B, hB⟩ := hηc.bounded_above_of_compact_support hηs
  set φ : G → ℂ := fun x => ∫ y, η y * ι v (x * y) ∂μ with hφdef
  have hφeq : φ = fun x => ∫ z, η (x⁻¹ * z) * ι v z ∂μ := by
    funext x
    rw [hφdef, ← integral_mul_left_eq_self (fun z => η (x⁻¹ * z) * ι v z) x]
    simp
  have hφc : Continuous φ := by
    rw [hφeq, continuous_iff_continuousAt]
    intro x₀
    obtain ⟨V, hV, hVn⟩ := exists_compact_mem_nhds x₀
    have hL : IsCompact (V * tsupport η) := hV.mul hηs
    refine continuousAt_of_dominated (bound := (V * tsupport η).indicator fun z => B * ‖ι v z‖)
      (Filter.Eventually.of_forall fun x =>
        ((hηc.comp (continuous_const.mul continuous_id)).aestronglyMeasurable).mul
          hιv.aestronglyMeasurable) ?_ ?_
      (Filter.Eventually.of_forall fun z =>
        ((hηc.comp (continuous_id.inv.mul continuous_const)).mul continuous_const).continuousAt)
    · filter_upwards [hVn] with x hx
      refine Filter.Eventually.of_forall fun z => ?_
      by_cases hz : η (x⁻¹ * z) = 0
      · rw [hz, zero_mul, norm_zero]
        exact Set.indicator_nonneg
          (fun _ _ => mul_nonneg ((norm_nonneg _).trans (hB 1)) (norm_nonneg _)) _
      have hzL : z ∈ V * tsupport η := by
        have := Set.mul_mem_mul hx (subset_tsupport η hz)
        rwa [mul_inv_cancel_left] at this
      rw [Set.indicator_of_mem hzL, norm_mul]
      exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
    · exact IntegrableOn.integrable_indicator
        ((hιv.integrableOn_isCompact hL).norm.const_mul B) hL.measurableSet
  refine ⟨φ, hφc, _root_.GlobalTheory.LocRep.rep_of_pairing hloc hφc.locallyIntegrable ?_⟩
  intro C hC
  obtain ⟨Λ, hΛ⟩ := _root_.GlobalTheory.LocRep.exists_pairing hloc hlin hC
  obtain ⟨M, hM⟩ := hloc C hC
  have hint : Integrable (fun y => η y • ρ y v) μ :=
    (hηc.smul (hcont v)).integrable_of_hasCompactSupport hηs.smul_right
  have hηI : Integrable η μ := hηc.integrable_of_hasCompactSupport hηs
  have hrestr : μ.prod (μ.restrict C) = (μ.prod μ).restrict (Set.univ ×ˢ C) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hmeas : AEStronglyMeasurable (fun p : G × G => η p.1 * ι v (p.2 * p.1))
      (μ.prod (μ.restrict C)) := by
    have h1 : AEStronglyMeasurable (fun p : G × G => ι v (p.2 * p.1)) (μ.prod μ) :=
      (hιv.aestronglyMeasurable.comp_snd (μ := μ)).comp_measurePreserving
        (measurePreserving_prod_mul_swap μ μ)
    rw [hrestr]
    exact ((hηc.comp continuous_fst).aestronglyMeasurable).mul h1.restrict
  have hslice : ∀ y, IntegrableOn (fun x => ι v (x * y)) C μ ∧
      ∫ x in C, ‖ι v (x * y)‖ ∂μ ≤ M * ‖v‖ := by
    intro y
    have hae : ι (ρ y v) =ᵐ[μ.restrict C] fun x => ι v (x * y) := ae_restrict_of_ae (htrans y v)
    obtain ⟨h1, h2⟩ := hM (ρ y v)
    refine ⟨h1.congr_fun_ae hae, ?_⟩
    rw [← hnorm y v]
    refine le_of_eq_of_le (integral_congr_ae (hae.mono fun x hx => ?_)).symm h2
    simp only [hx]
  have hprod : Integrable (Function.uncurry fun y x => η y * ι v (x * y))
      (μ.prod (μ.restrict C)) := by
    refine (integrable_prod_iff hmeas).2 ⟨Filter.Eventually.of_forall fun y =>
      (hslice y).1.const_mul (η y), ?_⟩
    refine Integrable.mono' (hηI.norm.mul_const (M * ‖v‖)) hmeas.norm.integral_prod_right' ?_
    refine Filter.Eventually.of_forall fun y => ?_
    simp only [norm_mul, Function.uncurry_apply_pair]
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => by positivity), integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hslice y).2 (norm_nonneg _)
  calc ∫ x in C, ι (∫ y, η y • ρ y v ∂μ) x ∂μ = Λ (∫ y, η y • ρ y v ∂μ) := (hΛ _).symm
    _ = ∫ y, Λ (η y • ρ y v) ∂μ := (Λ.integral_comp_comm hint).symm
    _ = ∫ y, ∫ x in C, η y * ι v (x * y) ∂μ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only
        rw [map_smul, hΛ, smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_of_ae (htrans y v)] with x hx
        rw [hx]
    _ = ∫ x in C, φ x ∂μ := integral_integral_swap hprod

end GlobalTheory.LocRep

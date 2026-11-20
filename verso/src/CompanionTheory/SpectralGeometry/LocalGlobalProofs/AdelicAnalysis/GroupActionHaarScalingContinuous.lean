import Mathlib

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic.ModulusAction

/- English proof (translation)
Introduce `V _ _ _ _ _ _ _ _ μ _ T _ _ _ _ a ha hinv h1 hmul`. Establish `hat : ∀ t, Continuous (a t)` using `fun t => by`. Establish `h` using `ha.comp (continuous_const.prodMk (continuous_id (X := V)) : Continuous fun y : V => (t, y))`. Conclude with `h`. Establish `hleft : ∀ t y, a t⁻¹ (a t y) = y`.

Introduce `t y`. Rewrite using `[← hmul, inv_mul_cancel, h1]`. Establish `hright : ∀ t y, a t (a t⁻¹ y) = y`. Introduce `t y`. Rewrite using `[← hmul, mul_inv_cancel, h1]`.

Establish `hfin : ∀ t, IsFiniteMeasureOnCompacts (μ.map (a t))`. Introduce `t`. Use `⟨fun K hK => ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.map_apply (hat t).measurable hK.isClosed.measurableSet]`. Use `lt_of_le_of_lt (measure_mono ?_) ((hK.image (hat t⁻¹)).measure_lt_top)` and prove the remaining obligations.

Introduce `y hy`. Conclude with `⟨a t y, hy, hleft t y⟩`. Establish `hinvar : ∀ t, (μ.map (a t)).IsAddLeftInvariant`. Introduce `t`. Use `⟨fun g => ?_⟩` and prove the remaining obligations.

Rewrite using `[Measure.map_map (measurable_const_add g) (hat t).measurable]`. Establish `e : (fun x => g + x) ∘ a t = a t ∘ fun x => a t⁻¹ g + x`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply, map_add, hright]`. Rewrite using `[e, ← Measure.map_map (hat t).measurable (measurable_const_add _), map_add_left_eq_self]`.

Establish `hscale : ∀ t, ∃ c : ℝ≥0, μ.map (a t) = c • μ`. Introduce `t`. Use `haveI := hfin t`. Use `haveI := hinvar t`. Conclude with `⟨_, Measure.isAddLeftInvariant_eq_smul _ μ⟩`.

Use `choose c hc using hscale`. Take `⟨f, hfc, hf0, hfx⟩` from `exists_continuous_nonneg_pos (0 : V)`. Establish `hI : 0 < ∫ y, f y ∂μ` using `f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc hf0 hfx`. Establish `hint : ∀ t (g : V → ℝ), Continuous g → ∫ y, g (a t y) ∂μ = (c t : ℝ) * ∫ y, g y ∂μ`. Introduce `t g hg`.

Rewrite using `[← integral_map (hat t).measurable.aemeasurable hg.aestronglyMeasurable, hc t, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]`. Establish `hform : ∀ t, (c t : ℝ) * ∫ y, f y ∂μ = ∫ y, f (a t y) ∂μ` using `fun t => (hint t f f.continuous).symm`. Establish `hone : c 1 = 1`. Apply `NNReal.coe_injective` to reduce the goal to its premises. Apply `mul_right_cancel₀ hI.ne'` to reduce the goal to its premises.

Rewrite using `[hform, NNReal.coe_one, one_mul]`. Simplify using `only [h1]`. Establish `hmulc : ∀ s t, c (s * t) = c s * c t`. Introduce `s t`. Apply `NNReal.coe_injective` to reduce the goal to its premises.

Apply `mul_right_cancel₀ hI.ne'` to reduce the goal to its premises. Rewrite using `[hform, NNReal.coe_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hF : Continuous fun t => ∫ y, f (a t y) ∂μ`. Use `continuous_iff_continuousAt.2 fun t₀ => ?_` and prove the remaining obligations.

Take `⟨N, hN, hNn⟩` from `exists_compact_mem_nhds t₀`. Use `set s : Set V := (fun p : T × V => a p.1 p.2) '' (((fun t => t⁻¹) '' N) ×ˢ tsupport f) with hsdef`. Establish `hs : IsCompact s` using `((hN.image hinv).prod hfc.isCompact).image ha`. Establish `hG : Continuous fun t => ∫ y in s, f (a t y) ∂μ`. Use `continuous_parametric_integral_of_continuous ?_ hs` and prove the remaining obligations.

Conclude with `f.continuous.comp ha`. Use `hG.continuousAt.congr (Filter.eventually_of_mem hNn fun t ht => ?_)` and prove the remaining obligations. Use `setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Conclude with `hy ⟨(t⁻¹, a t y), ⟨⟨t, ht, rfl⟩, subset_tsupport _ hne⟩, hleft t y⟩`.

Establish `hcreal : (fun t => (c t : ℝ)) = fun t => (∫ y, f (a t y) ∂μ) / ∫ y, f y ∂μ`. Use function extensionality and compare the values at `fun t => eq_div_of_mul_eq hI.ne' (hform t)`. Use `⟨{ toFun := c, map_one' := hone, map_mul' := hmulc }, ?_, hc⟩` and prove the remaining obligations. Use `show Continuous c`. Establish `hcont : Continuous fun t => (c t : ℝ)`.

Rewrite using `[hcreal]`. Conclude with `hF.div_const _`. Conclude with `Continuous.subtype_mk hcont fun t => (c t).2`.
-/
theorem exists_continuous_modulus :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
      [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
      (μ : Measure V) [μ.IsAddHaarMeasure] (T : Type) [Group T] [TopologicalSpace T]
      [FirstCountableTopology T] [LocallyCompactSpace T] (a : T → V →+ V),
      (Continuous fun p : T × V => a p.1 p.2) → Continuous (fun t : T => t⁻¹) →
      (∀ y, a 1 y = y) → (∀ s t y, a (s * t) y = a s (a t y)) →
      ∃ χ : T →* ℝ≥0, Continuous χ ∧ ∀ t, μ.map (a t) = χ t • μ := by
  intro V _ _ _ _ _ _ _ _ μ _ T _ _ _ _ a ha hinv h1 hmul
  have hat : ∀ t, Continuous (a t) := fun t => by
    have h := ha.comp (continuous_const.prodMk (continuous_id (X := V)) :
      Continuous fun y : V => (t, y))
    exact h
  have hleft : ∀ t y, a t⁻¹ (a t y) = y := by
    intro t y
    rw [← hmul, inv_mul_cancel, h1]
  have hright : ∀ t y, a t (a t⁻¹ y) = y := by
    intro t y
    rw [← hmul, mul_inv_cancel, h1]
  have hfin : ∀ t, IsFiniteMeasureOnCompacts (μ.map (a t)) := by
    intro t
    refine ⟨fun K hK => ?_⟩
    rw [Measure.map_apply (hat t).measurable hK.isClosed.measurableSet]
    refine lt_of_le_of_lt (measure_mono ?_) ((hK.image (hat t⁻¹)).measure_lt_top)
    intro y hy
    exact ⟨a t y, hy, hleft t y⟩
  have hinvar : ∀ t, (μ.map (a t)).IsAddLeftInvariant := by
    intro t
    refine ⟨fun g => ?_⟩
    rw [Measure.map_map (measurable_const_add g) (hat t).measurable]
    have e : (fun x => g + x) ∘ a t = a t ∘ fun x => a t⁻¹ g + x := by
      funext x
      simp only [Function.comp_apply, map_add, hright]
    rw [e, ← Measure.map_map (hat t).measurable (measurable_const_add _),
      map_add_left_eq_self]
  have hscale : ∀ t, ∃ c : ℝ≥0, μ.map (a t) = c • μ := by
    intro t
    haveI := hfin t
    haveI := hinvar t
    exact ⟨_, Measure.isAddLeftInvariant_eq_smul _ μ⟩
  choose c hc using hscale
  obtain ⟨f, hfc, hf0, hfx⟩ := exists_continuous_nonneg_pos (0 : V)
  have hI : 0 < ∫ y, f y ∂μ :=
    f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc hf0 hfx
  have hint : ∀ t (g : V → ℝ), Continuous g →
      ∫ y, g (a t y) ∂μ = (c t : ℝ) * ∫ y, g y ∂μ := by
    intro t g hg
    rw [← integral_map (hat t).measurable.aemeasurable hg.aestronglyMeasurable, hc t,
      integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
  have hform : ∀ t, (c t : ℝ) * ∫ y, f y ∂μ = ∫ y, f (a t y) ∂μ := fun t =>
    (hint t f f.continuous).symm
  have hone : c 1 = 1 := by
    apply NNReal.coe_injective
    apply mul_right_cancel₀ hI.ne'
    rw [hform, NNReal.coe_one, one_mul]
    simp only [h1]
  have hmulc : ∀ s t, c (s * t) = c s * c t := by
    intro s t
    apply NNReal.coe_injective
    apply mul_right_cancel₀ hI.ne'
    rw [hform, NNReal.coe_mul]
    calc ∫ y, f (a (s * t) y) ∂μ = ∫ y, f (a s (a t y)) ∂μ := by simp only [hmul]
      _ = (c t : ℝ) * ∫ y, f (a s y) ∂μ := hint t (fun z => f (a s z)) (f.continuous.comp (hat s))
      _ = (c s : ℝ) * (c t : ℝ) * ∫ y, f y ∂μ := by rw [← hform s]; ring
  have hF : Continuous fun t => ∫ y, f (a t y) ∂μ := by
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    obtain ⟨N, hN, hNn⟩ := exists_compact_mem_nhds t₀
    set s : Set V := (fun p : T × V => a p.1 p.2) '' (((fun t => t⁻¹) '' N) ×ˢ tsupport f)
      with hsdef
    have hs : IsCompact s := ((hN.image hinv).prod hfc.isCompact).image ha
    have hG : Continuous fun t => ∫ y in s, f (a t y) ∂μ := by
      refine continuous_parametric_integral_of_continuous ?_ hs
      exact f.continuous.comp ha
    refine hG.continuousAt.congr (Filter.eventually_of_mem hNn fun t ht => ?_)
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    by_contra hne
    exact hy ⟨(t⁻¹, a t y), ⟨⟨t, ht, rfl⟩, subset_tsupport _ hne⟩, hleft t y⟩
  have hcreal : (fun t => (c t : ℝ)) = fun t => (∫ y, f (a t y) ∂μ) / ∫ y, f y ∂μ :=
    funext fun t => eq_div_of_mul_eq hI.ne' (hform t)
  refine ⟨{ toFun := c, map_one' := hone, map_mul' := hmulc }, ?_, hc⟩
  show Continuous c
  have hcont : Continuous fun t => (c t : ℝ) := by
    rw [hcreal]
    exact hF.div_const _
  exact Continuous.subtype_mk hcont fun t => (c t).2

end GlobalTheory.CompanionTheory.Adelic.ModulusAction

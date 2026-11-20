import Mathlib
import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousDensitiesEqOfIntegralsOnCompactsStatement

open MeasureTheory Topology Matrix Set
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.FibreUniq

/- English proof (translation)
Establish `hK : ∀ K : Set V, IsCompact K → K ⊆ O → m.restrict K = m'.restrict K`. Introduce `K hK hKO`. Take `⟨χ, h1, hc, hs, h01⟩` from `exists_continuousMap_one_of_isCompact_subset_isOpen hK hO hKO`. Establish `hχm : Measurable fun v => ENNReal.ofReal (χ v)` using `ENNReal.measurable_ofReal.comp χ.continuous.measurable`. Establish `hint` using `(h χ χ.continuous hc hs (fun v => (h01 v).1)).1`.

Use `haveI : IsFiniteMeasure (m.withDensity fun v => ENNReal.ofReal (χ v)) := isFiniteMeasure_withDensity_ofReal hint.2`. Establish `key : (m.withDensity fun v => ENNReal.ofReal (χ v)) = m'.withDensity fun v => ENNReal.ofReal (χ v)`. Apply `ext_of_forall_lintegral_eq_of_IsFiniteMeasure` to reduce the goal to its premises. Introduce `g`. Establish `hg : Measurable fun v => (g v : ℝ≥0∞)` using `measurable_coe_nnreal_ennreal.comp g.continuous.measurable`.

Rewrite using `[lintegral_withDensity_eq_lintegral_mul _ hχm hg, lintegral_withDensity_eq_lintegral_mul _ hχm hg]`. Use `(h (fun v => χ v * (g v : ℝ)) (χ.continuous.mul (NNReal.continuous_coe.comp g.continuous)) (HasCompactSupport.mul_right (f := fun v => χ v) hc) ((tsupport_mul_subset_left (f := fun v => χ v)).trans hs) (fun v => mul_nonneg (h01 v).1 (g v).2)).2` as an intermediate fact. Establish `e : ∀ v, ENNReal.ofReal (χ v * (g v : ℝ)) = ENNReal.ofReal (χ v) * (g v : ℝ≥0∞)`. Introduce `v`. Rewrite using `[ENNReal.ofReal_mul (h01 v).1, ENNReal.ofReal_coe_nnreal]`.

Simplify `this` using `only [e, Pi.mul_apply]`. Establish `aux : ∀ n : Measure V, (n.withDensity fun v => ENNReal.ofReal (χ v)).restrict K = n.restrict K`. Introduce `n`. Rewrite using `[restrict_withDensity hK.measurableSet]`. Establish `: (fun v => ENNReal.ofReal (χ v)) =ᵐ[n.restrict K] 1` using `by filter_upwards [ae_restrict_mem hK.measurableSet] with v hv`.

Simplify using `[h1 hv]`. Rewrite using `[withDensity_congr_ae this, withDensity_one]`. Rewrite using `[← aux m, ← aux m', key]`. Establish `hx : ∀ x ∈ O, ∃ K : Set V, K ∈ 𝓝[O] x ∧ IsCompact K ∧ K ⊆ O`. Introduce `x hx`.

Take `⟨K, hK1, hK2, hK3⟩` from `local_compact_nhds (hO.mem_nhds hx)`. Conclude with `⟨K, mem_nhdsWithin_of_mem_nhds hK1, hK3, hK2⟩`. Use `choose! K hK1 hK2 hK3 using hx`. Take `⟨s, hsO, hsc, hcov⟩` from `TopologicalSpace.countable_cover_nhdsWithin hK1`. Establish `hU : m.restrict (⋃ x ∈ s, K x) = m'.restrict (⋃ x ∈ s, K x)` using `(Measure.restrict_biUnion_congr hsc).2 fun x hx => hK _ (hK2 x (hsO hx)) (hK3 x (hsO hx))`.

Establish `r : ∀ n : Measure V, n Oᶜ = 0 → n.restrict (⋃ x ∈ s, K x) = n`. Introduce `n hn`. Apply `Measure.restrict_eq_self_of_ae_mem` to reduce the goal to its premises. Establish `: ∀ᵐ v ∂n, v ∈ O` using `hn`. Use `filter_upwards [this] with v hv using hcov hv`.

Rewrite using `[← r m hm, ← r m' hm', hU]`.
-/
theorem measure_eq_of_lintegral_eq {V : Type} [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    (m m' : Measure V) (O : Set V) (hO : IsOpen O) (hm : m Oᶜ = 0) (hm' : m' Oᶜ = 0)
    (h : ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ O → (∀ v, 0 ≤ φ v) →
      Integrable φ m ∧ ∫⁻ v, ENNReal.ofReal (φ v) ∂m = ∫⁻ v, ENNReal.ofReal (φ v) ∂m') :
    m = m' := by
  have hK : ∀ K : Set V, IsCompact K → K ⊆ O → m.restrict K = m'.restrict K := by
    intro K hK hKO
    obtain ⟨χ, h1, hc, hs, h01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hO hKO
    have hχm : Measurable fun v => ENNReal.ofReal (χ v) :=
      ENNReal.measurable_ofReal.comp χ.continuous.measurable
    have hint := (h χ χ.continuous hc hs (fun v => (h01 v).1)).1
    haveI : IsFiniteMeasure (m.withDensity fun v => ENNReal.ofReal (χ v)) :=
      isFiniteMeasure_withDensity_ofReal hint.2
    have key : (m.withDensity fun v => ENNReal.ofReal (χ v)) =
        m'.withDensity fun v => ENNReal.ofReal (χ v) := by
      apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
      intro g
      have hg : Measurable fun v => (g v : ℝ≥0∞) :=
        measurable_coe_nnreal_ennreal.comp g.continuous.measurable
      rw [lintegral_withDensity_eq_lintegral_mul _ hχm hg,
        lintegral_withDensity_eq_lintegral_mul _ hχm hg]
      have := (h (fun v => χ v * (g v : ℝ))
        (χ.continuous.mul (NNReal.continuous_coe.comp g.continuous))
        (HasCompactSupport.mul_right (f := fun v => χ v) hc)
        ((tsupport_mul_subset_left (f := fun v => χ v)).trans hs)
        (fun v => mul_nonneg (h01 v).1 (g v).2)).2
      have e : ∀ v, ENNReal.ofReal (χ v * (g v : ℝ)) = ENNReal.ofReal (χ v) * (g v : ℝ≥0∞) := by
        intro v
        rw [ENNReal.ofReal_mul (h01 v).1, ENNReal.ofReal_coe_nnreal]
      simpa only [e, Pi.mul_apply] using this
    have aux : ∀ n : Measure V, (n.withDensity fun v => ENNReal.ofReal (χ v)).restrict K
        = n.restrict K := by
      intro n
      rw [restrict_withDensity hK.measurableSet]
      have : (fun v => ENNReal.ofReal (χ v)) =ᵐ[n.restrict K] 1 := by
        filter_upwards [ae_restrict_mem hK.measurableSet] with v hv
        simp [h1 hv]
      rw [withDensity_congr_ae this, withDensity_one]
    rw [← aux m, ← aux m', key]
  have hx : ∀ x ∈ O, ∃ K : Set V, K ∈ 𝓝[O] x ∧ IsCompact K ∧ K ⊆ O := by
    intro x hx
    obtain ⟨K, hK1, hK2, hK3⟩ := local_compact_nhds (hO.mem_nhds hx)
    exact ⟨K, mem_nhdsWithin_of_mem_nhds hK1, hK3, hK2⟩
  choose! K hK1 hK2 hK3 using hx
  obtain ⟨s, hsO, hsc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin hK1
  have hU : m.restrict (⋃ x ∈ s, K x) = m'.restrict (⋃ x ∈ s, K x) :=
    (Measure.restrict_biUnion_congr hsc).2 fun x hx => hK _ (hK2 x (hsO hx)) (hK3 x (hsO hx))
  have r : ∀ n : Measure V, n Oᶜ = 0 → n.restrict (⋃ x ∈ s, K x) = n := by
    intro n hn
    apply Measure.restrict_eq_self_of_ae_mem
    have : ∀ᵐ v ∂n, v ∈ O := hn
    filter_upwards [this] with v hv using hcov hv
  rw [← r m hm, ← r m' hm', hU]

/- English proof (translation)
Establish `: ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {ι b} ∩ U` using `h.1 b`. Use `filter_upwards [this] with v hv`. Use `⟨hι ?_, hv.2⟩` and prove the remaining obligations. Rewrite using `[← hf v]`. Conclude with `hv.1`.
-/
theorem ae_eq_of_isFibreFamily {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
    [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {ν : Measure X} {f : V → Y}
    {g : V → X} {ι : X → Y} (hι : Function.Injective ι) (hf : ∀ v, f v = ι (g v))
    {U : Set V} {B : Set X} {fib : X → Measure V}
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib) (b : X) :
    ∀ᵐ v ∂(fib b), g v = b ∧ v ∈ U := by
  have : ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {ι b} ∩ U := h.1 b
  filter_upwards [this] with v hv
  refine ⟨hι ?_, hv.2⟩
  rw [← hf v]
  exact hv.1

/- English proof (translation)
Establish `h2` using `h.2.1 ((g ⁻¹' S).indicator φ) (hφ.indicator (hg.measurable hS))`. Establish `e1 : ∫⁻ v in U, (g ⁻¹' S).indicator φ v ∂μ = ∫⁻ v in O, (g ⁻¹' S).indicator φ v ∂μ`. Establish `: (g ⁻¹' S).indicator φ = O.indicator ((g ⁻¹' S).indicator φ)`. Use function extensionality and compare the values at `v`. Distinguish the cases in `hv : v ∈ O`.

Rewrite using `[indicator_of_mem hv]`. Rewrite using `[indicator_of_notMem hv]`. Conclude with `indicator_apply_eq_zero.2 fun _ => hs v hv`. Use `conv_lhs => rw [this]`. Rewrite using `[lintegral_indicator hO.measurableSet, Measure.restrict_restrict hO.measurableSet, inter_eq_left.2 hU]`.

Rewrite using `[← e1, h2, ← lintegral_indicator hS]`. Use `congr 1`. Use function extensionality and compare the values at `b`. Establish `hb` using `ae_eq_of_isFibreFamily hι hf h b`. Distinguish the cases in `hbS : b ∈ S`.

Rewrite using `[indicator_of_mem hbS]`. Apply `lintegral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hb] with v hv`. Conclude with `indicator_of_mem (by simpa [mem_preimage, hv.1] using hbS) _`. Rewrite using `[indicator_of_notMem hbS, ← lintegral_zero (μ := fib b)]`.

Apply `lintegral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hb] with v hv`. Conclude with `indicator_of_notMem (by simpa [mem_preimage, hv.1] using hbS) _`.
-/
theorem lintegral_preimage {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] {μ : Measure V} {ν : Measure X}
    {f : V → Y} {g : V → X} {ι : X → Y} (hι : Function.Injective ι) (hg : Continuous g)
    (hf : ∀ v, f v = ι (g v)) {O U : Set V} {B : Set X} {fib : X → Measure V}
    (hO : IsOpen O) (hU : O ⊆ U) (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib)
    (φ : V → ℝ≥0∞) (hφ : Measurable φ) (hs : ∀ v, v ∉ O → φ v = 0)
    (S : Set X) (hS : MeasurableSet S) :
    ∫⁻ v in O, (g ⁻¹' S).indicator φ v ∂μ = ∫⁻ b in S, ∫⁻ v, φ v ∂(fib b) ∂ν := by
  have h2 := h.2.1 ((g ⁻¹' S).indicator φ) (hφ.indicator (hg.measurable hS))
  have e1 : ∫⁻ v in U, (g ⁻¹' S).indicator φ v ∂μ = ∫⁻ v in O, (g ⁻¹' S).indicator φ v ∂μ := by
    have : (g ⁻¹' S).indicator φ = O.indicator ((g ⁻¹' S).indicator φ) := by
      funext v
      by_cases hv : v ∈ O
      · rw [indicator_of_mem hv]
      · rw [indicator_of_notMem hv]
        exact indicator_apply_eq_zero.2 fun _ => hs v hv
    conv_lhs => rw [this]
    rw [lintegral_indicator hO.measurableSet, Measure.restrict_restrict hO.measurableSet,
      inter_eq_left.2 hU]
  rw [← e1, h2, ← lintegral_indicator hS]
  congr 1
  funext b
  have hb := ae_eq_of_isFibreFamily hι hf h b
  by_cases hbS : b ∈ S
  · rw [indicator_of_mem hbS]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact indicator_of_mem (by simpa [mem_preimage, hv.1] using hbS) _
  · rw [indicator_of_notMem hbS, ← lintegral_zero (μ := fib b)]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact indicator_of_notMem (by simpa [mem_preimage, hv.1] using hbS) _

/- English proof (translation)
Establish `hO : IsOpen (g ⁻¹' B')` using `hB'.preimage hg`. Establish `hOU : g ⁻¹' B' ⊆ g ⁻¹' B` using `preimage_mono hBB`. Establish `carried : ∀ n : Measure V, (∀ᵐ v ∂n, g v = b) → n (g ⁻¹' B')ᶜ = 0`. Introduce `n hn`. Establish `: ∀ᵐ v ∂n, v ∈ g ⁻¹' B'` using `by filter_upwards [hn] with v hv`.

Simplify `hb` using `[mem_preimage, hv]`. Conclude with `this`. Use `measure_eq_of_lintegral_eq _ _ (g ⁻¹' B') hO (carried _ ((ae_eq_of_isFibreFamily hι hf h' b).mono fun _ hv => hv.1)) (carried _ ((ae_eq_of_isFibreFamily hι hf h b).mono fun _ hv => hv.1)) ?_` and prove the remaining obligations. Introduce `φ hφ hc hs h0`. Take `⟨hi, hc1⟩` from `h.2.2 φ hφ hc (hs.trans hOU)`.

Take `⟨hi', hc2⟩` from `h'.2.2 φ hφ hc hs`. Use `⟨hi' b hb, ?_⟩` and prove the remaining obligations. Establish `hφm : Measurable fun v => ENNReal.ofReal (φ v)` using `ENNReal.measurable_ofReal.comp hφ.measurable`. Establish `hφ0 : ∀ v, v ∉ g ⁻¹' B' → ENNReal.ofReal (φ v) = 0`. Introduce `v hv`.

Rewrite using `[image_eq_zero_of_notMem_tsupport fun h => hv (hs h), ENNReal.ofReal_zero]`. Establish `c : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) B'` using `(ENNReal.continuous_ofReal.comp_continuousOn (hc1.mono hBB)).congr fun b hb => (ofReal_integral_eq_lintegral_ofReal (hi b (hBB hb)) (Filter.Eventually.of_forall h0)).symm`. Establish `c' : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' b)) B'` using `(ENNReal.continuous_ofReal.comp_continuousOn hc2).congr fun b hb => (ofReal_integral_eq_lintegral_ofReal (hi' b hb) (Filter.Eventually.of_forall h0)).symm`. Use `GlobalTheory.T.continuous_densities_eq_of_integrals_on_compacts X ν B' hB' _ _ c' c (fun S hS _ => ?_) b hb` and prove the remaining obligations. Rewrite using `[← lintegral_preimage hι hg hf hO subset_rfl h' _ hφm hφ0 S hS.measurableSet, ← lintegral_preimage hι hg hf hO hOU h _ hφm hφ0 S hS.measurableSet]`.
-/
theorem fibreFamily_eq (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure]
    (f : V → Y) (g : V → X) (ι : X → Y) (hι : Function.Injective ι) (hg : Continuous g)
    (hf : ∀ v, f v = ι (g v)) (B B' : Set X) (hB : IsOpen B) (hB' : IsOpen B') (hBB : B' ⊆ B)
    (fib fib' : X → Measure V)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib)
    (h' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B') ν B' fib')
    (b : X) (hb : b ∈ B') : fib' b = fib b := by
  have hO : IsOpen (g ⁻¹' B') := hB'.preimage hg
  have hOU : g ⁻¹' B' ⊆ g ⁻¹' B := preimage_mono hBB
  have carried : ∀ n : Measure V, (∀ᵐ v ∂n, g v = b) → n (g ⁻¹' B')ᶜ = 0 := by
    intro n hn
    have : ∀ᵐ v ∂n, v ∈ g ⁻¹' B' := by
      filter_upwards [hn] with v hv
      simpa [mem_preimage, hv] using hb
    exact this
  refine measure_eq_of_lintegral_eq _ _ (g ⁻¹' B') hO
    (carried _ ((ae_eq_of_isFibreFamily hι hf h' b).mono fun _ hv => hv.1))
    (carried _ ((ae_eq_of_isFibreFamily hι hf h b).mono fun _ hv => hv.1)) ?_
  intro φ hφ hc hs h0
  obtain ⟨hi, hc1⟩ := h.2.2 φ hφ hc (hs.trans hOU)
  obtain ⟨hi', hc2⟩ := h'.2.2 φ hφ hc hs
  refine ⟨hi' b hb, ?_⟩
  have hφm : Measurable fun v => ENNReal.ofReal (φ v) :=
    ENNReal.measurable_ofReal.comp hφ.measurable
  have hφ0 : ∀ v, v ∉ g ⁻¹' B' → ENNReal.ofReal (φ v) = 0 := by
    intro v hv
    rw [image_eq_zero_of_notMem_tsupport fun h => hv (hs h), ENNReal.ofReal_zero]
  have c : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) B' :=
    (ENNReal.continuous_ofReal.comp_continuousOn (hc1.mono hBB)).congr fun b hb =>
      (ofReal_integral_eq_lintegral_ofReal (hi b (hBB hb)) (Filter.Eventually.of_forall h0)).symm
  have c' : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' b)) B' :=
    (ENNReal.continuous_ofReal.comp_continuousOn hc2).congr fun b hb =>
      (ofReal_integral_eq_lintegral_ofReal (hi' b hb) (Filter.Eventually.of_forall h0)).symm
  refine GlobalTheory.T.continuous_densities_eq_of_integrals_on_compacts X ν B' hB' _ _ c' c (fun S hS _ => ?_) b hb
  rw [← lintegral_preimage hι hg hf hO subset_rfl h' _ hφm hφ0 S hS.measurableSet,
    ← lintegral_preimage hι hg hf hO hOU h _ hφm hφ0 S hS.measurableSet]

end GlobalTheory.CompanionTheory.SW.FibreUniq

import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SiegelWeilVolume.FibMeas0Holds

noncomputable section

namespace PI.DegenerateSiegelWeil.Scale

open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal NNReal

section Reindex

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} {U : Set V} {fib : X → Measure V}

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hfib`. Establish `hme : ⇑e.toMeasurableEquiv = ⇑e` using `rfl`. Establish `hμ' : μ.map e.toMeasurableEquiv = cμ • μ` using `hμ`. Establish `hν' : ν.map h.symm.toMeasurableEquiv = cν • ν` using `hν`. Establish `hpre : ∀ b, e ⁻¹' (f ⁻¹' {ι b} ∩ U) = f ⁻¹' {ι (h.symm b)} ∩ U`.

Introduce `b`. Use extensionality with `v`. Establish `hUv : e v ∈ U ↔ v ∈ U` using `by conv_rhs => rw [← hU]`. Conclude with `Iff.rfl`. Simplify using `only [mem_preimage, mem_inter_iff, mem_singleton_iff, hff', heh, hι.eq_iff, hUv]`.

Rewrite using `[h.eq_symm_apply]`. Use `⟨fun b => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩` and prove the remaining obligations. Rewrite using `[MeasurableEquiv.map_apply, preimage_compl, hme, hpre]`. Conclude with `h1 (h.symm b)`. Rewrite using `[Measure.restrict_smul, lintegral_smul_measure]`.

Establish `hφe : Measurable (φ ∘ e)` using `hφ.comp e.continuous.measurable`. Establish `key1 : ∫⁻ v in U, (φ ∘ e) v ∂μ = cμ * ∫⁻ v in U, φ v ∂μ`. Establish `h0 : ∫⁻ v in U, φ v ∂(μ.map e.toMeasurableEquiv) = ∫⁻ v in U, (φ ∘ e) v ∂μ`. Rewrite using `[MeasurableEquiv.restrict_map, lintegral_map_equiv, hme, hU]`. Both sides reduce to the same expression.

Rewrite using `[← h0, hμ', Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]`. Establish `key2 : ∫⁻ b, ∫⁻ v, φ v ∂(fib (h.symm b)).map e.toMeasurableEquiv ∂ν = cν * ∫⁻ b, ∫⁻ v, (φ ∘ e) v ∂fib b ∂ν`. Simplify using `only [lintegral_map_equiv]`. Rewrite using `[← smul_eq_mul, ← lintegral_smul_measure, ← hν', lintegral_map_equiv]`. Both sides reduce to the same expression.

Rewrite using `[key2, ← h2 _ hφe, key1, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hφe_c : Continuous (φ ∘ e)` using `hφc.comp e.continuous`. Establish `hφe_s : HasCompactSupport (φ ∘ e)` using `hφs.comp_homeomorph e`. Establish `hsub : tsupport (φ ∘ e) ⊆ e ⁻¹' tsupport φ` using `closure_minimal (fun v hv => subset_tsupport φ hv) ((isClosed_tsupport φ).preimage e.continuous)`.

Establish `hφe_U : tsupport (φ ∘ e) ⊆ U`. Introduce `v hv`. Rewrite using `[← hU]`. Conclude with `hφU (hsub hv)`. Take `⟨hi, hcont⟩` from `h3 _ hφe_c hφe_s hφe_U`.

Use `⟨fun b _ => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[integrable_map_equiv]`. Conclude with `hi _ (mem_univ _)`. Establish `hfun : (fun b => ∫ v, φ v ∂(fib (h.symm b)).map e.toMeasurableEquiv) = (fun b' => ∫ v, (φ ∘ e) v ∂fib b') ∘ h.symm`. Use function extensionality and compare the values at `b`.

Simplify using `only [Function.comp_apply, integral_map_equiv]`. Both sides reduce to the same expression. Rewrite using `[hfun]`. Conclude with `((continuousOn_univ.1 hcont).comp h.symm.continuous).continuousOn`.
-/
theorem isFibreFamily_reindex (e : V ≃ₜ V) (h : X ≃ₜ X) {f' : V → X}
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (heh : ∀ v, f' (e v) = h (f' v)) (hU : e ⁻¹' U = U) {cμ cν : ℝ≥0∞}
    (hμ : μ.map e = cμ • μ) (hν : ν.map h.symm = cν • ν)
    (hfib : IsFibreFamily μ f ι U ν univ fib) :
    IsFibreFamily ((cμ * cν) • μ) f ι U ν univ
      (fun b => (fib (h.symm b)).map e.toMeasurableEquiv) := by
  obtain ⟨h1, h2, h3⟩ := hfib
  have hme : ⇑e.toMeasurableEquiv = ⇑e := rfl
  have hμ' : μ.map e.toMeasurableEquiv = cμ • μ := hμ
  have hν' : ν.map h.symm.toMeasurableEquiv = cν • ν := hν
  have hpre : ∀ b, e ⁻¹' (f ⁻¹' {ι b} ∩ U) = f ⁻¹' {ι (h.symm b)} ∩ U := by
    intro b
    ext v
    have hUv : e v ∈ U ↔ v ∈ U := by
      conv_rhs => rw [← hU]
      exact Iff.rfl
    simp only [mem_preimage, mem_inter_iff, mem_singleton_iff, hff', heh, hι.eq_iff, hUv]
    rw [h.eq_symm_apply]
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩
  · rw [MeasurableEquiv.map_apply, preimage_compl, hme, hpre]
    exact h1 (h.symm b)
  · rw [Measure.restrict_smul, lintegral_smul_measure]
    have hφe : Measurable (φ ∘ e) := hφ.comp e.continuous.measurable
    have key1 : ∫⁻ v in U, (φ ∘ e) v ∂μ = cμ * ∫⁻ v in U, φ v ∂μ := by
      have h0 : ∫⁻ v in U, φ v ∂(μ.map e.toMeasurableEquiv) = ∫⁻ v in U, (φ ∘ e) v ∂μ := by
        rw [MeasurableEquiv.restrict_map, lintegral_map_equiv, hme, hU]
        rfl
      rw [← h0, hμ', Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
    have key2 : ∫⁻ b, ∫⁻ v, φ v ∂(fib (h.symm b)).map e.toMeasurableEquiv ∂ν =
        cν * ∫⁻ b, ∫⁻ v, (φ ∘ e) v ∂fib b ∂ν := by
      simp only [lintegral_map_equiv]
      rw [← smul_eq_mul, ← lintegral_smul_measure, ← hν', lintegral_map_equiv]
      rfl
    rw [key2, ← h2 _ hφe, key1, smul_eq_mul]
    ring
  · have hφe_c : Continuous (φ ∘ e) := hφc.comp e.continuous
    have hφe_s : HasCompactSupport (φ ∘ e) := hφs.comp_homeomorph e
    have hsub : tsupport (φ ∘ e) ⊆ e ⁻¹' tsupport φ :=
      closure_minimal (fun v hv => subset_tsupport φ hv) ((isClosed_tsupport φ).preimage e.continuous)
    have hφe_U : tsupport (φ ∘ e) ⊆ U := by
      intro v hv
      rw [← hU]
      exact hφU (hsub hv)
    obtain ⟨hi, hcont⟩ := h3 _ hφe_c hφe_s hφe_U
    refine ⟨fun b _ => ?_, ?_⟩
    · rw [integrable_map_equiv]
      exact hi _ (mem_univ _)
    · have hfun : (fun b => ∫ v, φ v ∂(fib (h.symm b)).map e.toMeasurableEquiv) =
          (fun b' => ∫ v, (φ ∘ e) v ∂fib b') ∘ h.symm := by
        funext b
        simp only [Function.comp_apply, integral_map_equiv]
        rfl
      rw [hfun]
      exact ((continuousOn_univ.1 hcont).comp h.symm.continuous).continuousOn

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hfib`. Use `⟨fun b => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩` and prove the remaining obligations. Simplify using `[h1 b]`. Rewrite using `[Measure.restrict_smul, lintegral_smul_measure, h2 φ hφ, smul_eq_mul, ← lintegral_const_mul' _ _ hc]`. Simplify using `only [lintegral_smul_measure, smul_eq_mul]`.

Take `⟨hi, hcont⟩` from `h3 φ hφc hφs hφU`. Use `⟨fun b hb => (hi b hb).smul_measure hc, ?_⟩` and prove the remaining obligations. Simplify using `only [integral_smul_measure, smul_eq_mul]`. Conclude with `continuousOn_const.mul hcont`.
-/
theorem isFibreFamily_smul {B : Set X} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hfib : IsFibreFamily μ f ι U ν B fib) :
    IsFibreFamily (c • μ) f ι U ν B (fun b => c • fib b) := by
  obtain ⟨h1, h2, h3⟩ := hfib
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩
  · simp [h1 b]
  · rw [Measure.restrict_smul, lintegral_smul_measure, h2 φ hφ, smul_eq_mul, ← lintegral_const_mul' _ _ hc]
    simp only [lintegral_smul_measure, smul_eq_mul]
  · obtain ⟨hi, hcont⟩ := h3 φ hφc hφs hφU
    refine ⟨fun b hb => (hi b hb).smul_measure hc, ?_⟩
    simp only [integral_smul_measure, smul_eq_mul]
    exact continuousOn_const.mul hcont

end Reindex

section Uniq

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
  [LocallyCompactSpace X]
  {μ : Measure V} {ν : Measure X} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
  [ν.IsOpenPosMeasure]
  {f : V → Y} {ι : X → Y} {U : Set V} {fib : X → Measure V}

/- English proof (translation)
Establish `hc : cμ * cν ≠ ⊤` using `ENNReal.mul_ne_top hcμ hcν`. Use `haveI : IsFiniteMeasureOnCompacts ((cμ * cν) • μ) := IsFiniteMeasureOnCompacts.smul μ hc`. Use `PI.DegenerateSiegelWeil.FibUniq.fib_eq (isFibreFamily_reindex e h hff' hι heh hU hμ hν hfib) (isFibreFamily_smul hc hfib) hf' hff' hι hUo` as an intermediate fact. Conclude with `congrFun this b`.
-/
theorem fib_reindex_eq (e : V ≃ₜ V) (h : X ≃ₜ X) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (hUo : IsOpen U)
    (heh : ∀ v, f' (e v) = h (f' v)) (hU : e ⁻¹' U = U) {cμ cν : ℝ≥0∞} (hcμ : cμ ≠ ⊤)
    (hcν : cν ≠ ⊤) (hμ : μ.map e = cμ • μ) (hν : ν.map h.symm = cν • ν)
    (hfib : IsFibreFamily μ f ι U ν univ fib) (b : X) :
    (fib (h.symm b)).map e.toMeasurableEquiv = (cμ * cν) • fib b := by
  have hc : cμ * cν ≠ ⊤ := ENNReal.mul_ne_top hcμ hcν
  haveI : IsFiniteMeasureOnCompacts ((cμ * cν) • μ) := IsFiniteMeasureOnCompacts.smul μ hc
  have := PI.DegenerateSiegelWeil.FibUniq.fib_eq (isFibreFamily_reindex e h hff' hι heh hU hμ hν hfib)
    (isFibreFamily_smul hc hfib) hf' hff' hι hUo
  exact congrFun this b

/- English proof (translation)
Establish `hb' : h.symm b = b` using `h.symm_apply_eq.2 hb.symm`. Use `fib_reindex_eq e h hf' hff' hι hUo heh hU hcμ hcν hμ hν hfib b` as an intermediate fact. Rewrite `this` using `[hb']`. Then use the resulting hypothesis.
-/
theorem fib_map_fixed (e : V ≃ₜ V) (h : X ≃ₜ X) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (hUo : IsOpen U)
    (heh : ∀ v, f' (e v) = h (f' v)) (hU : e ⁻¹' U = U) {cμ cν : ℝ≥0∞} (hcμ : cμ ≠ ⊤)
    (hcν : cν ≠ ⊤) (hμ : μ.map e = cμ • μ) (hν : ν.map h.symm = cν • ν)
    (hfib : IsFibreFamily μ f ι U ν univ fib) (b : X) (hb : h b = b) :
    (fib b).map e.toMeasurableEquiv = (cμ * cν) • fib b := by
  have hb' : h.symm b = b := h.symm_apply_eq.2 hb.symm
  have := fib_reindex_eq e h hf' hff' hι hUo heh hU hcμ hcν hμ hν hfib b
  rwa [hb'] at this

end Uniq

end PI.DegenerateSiegelWeil.Scale

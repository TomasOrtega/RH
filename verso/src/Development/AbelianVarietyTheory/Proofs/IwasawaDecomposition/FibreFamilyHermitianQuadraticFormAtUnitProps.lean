import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.FibBasic

section General

variable {V X : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
  [MeasurableSpace X] {μ : Measure V} {f : V → X} {ν : Measure X} {B : Set X}

/- English proof (translation)
Establish `h2` using `h.2.1 ((f ⁻¹' S).indicator φ) (hφ.indicator (hf hS))`. Rewrite `h2` using `[Measure.restrict_univ]`. Rewrite using `[h2, ← lintegral_indicator hS]`. Use `congr 1`. Use function extensionality and compare the values at `b`.

Establish `hb : ∀ᵐ v ∂(fib b), f v = b`. Establish `: ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {id b} ∩ Set.univ` using `h.1 b`. Use `filter_upwards [this] with v hv using hv.1`. Distinguish the cases in `hbS : b ∈ S`. Rewrite using `[Set.indicator_of_mem hbS]`.

Apply `lintegral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hb] with v hv`. Conclude with `Set.indicator_of_mem (by simpa [hv] using hbS) _`. Rewrite using `[Set.indicator_of_notMem hbS, ← lintegral_zero (μ := fib b)]`. Apply `lintegral_congr_ae` to reduce the goal to its premises.

Use `filter_upwards [hb] with v hv`. Conclude with `Set.indicator_of_notMem (by simpa [hv] using hbS) _`.
-/
theorem lintegral_preimage {fib : X → Measure V} (hf : Measurable f)
    (h : IsFibreFamily μ f id Set.univ ν B fib) (φ : V → ℝ≥0∞) (hφ : Measurable φ)
    (S : Set X) (hS : MeasurableSet S) :
    ∫⁻ v, (f ⁻¹' S).indicator φ v ∂μ = ∫⁻ b in S, ∫⁻ v, φ v ∂(fib b) ∂ν := by
  have h2 := h.2.1 ((f ⁻¹' S).indicator φ) (hφ.indicator (hf hS))
  rw [Measure.restrict_univ] at h2
  rw [h2, ← lintegral_indicator hS]
  congr 1
  funext b
  have hb : ∀ᵐ v ∂(fib b), f v = b := by
    have : ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {id b} ∩ Set.univ := h.1 b
    filter_upwards [this] with v hv using hv.1
  by_cases hbS : b ∈ S
  · rw [Set.indicator_of_mem hbS]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact Set.indicator_of_mem (by simpa [hv] using hbS) _
  · rw [Set.indicator_of_notMem hbS, ← lintegral_zero (μ := fib b)]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact Set.indicator_of_notMem (by simpa [hv] using hbS) _

/- English proof (translation)
Use `⟨fun K hK => ?_⟩` and prove the remaining obligations. Take `⟨φ, h1, -, hc, h01⟩` from `exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty _)`. Establish `hi` using `(h.2.2 φ φ.continuous hc (Set.subset_univ _)).1 β hβ`. Use `lt_of_le_of_lt (measure_mono ?_) (hi.measure_ge_lt_top (ε := 1) one_pos)` and prove the remaining obligations. Introduce `v hv`.

Conclude with `(h1 hv).ge`.
-/
theorem finite_on_compacts [T2Space V] [LocallyCompactSpace V] [BorelSpace V]
    {fib : X → Measure V} (h : IsFibreFamily μ f id Set.univ ν B fib) {β : X} (hβ : β ∈ B) :
    IsFiniteMeasureOnCompacts (fib β) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨φ, h1, -, hc, h01⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty _)
  have hi := (h.2.2 φ φ.continuous hc (Set.subset_univ _)).1 β hβ
  refine lt_of_le_of_lt (measure_mono ?_) (hi.measure_ge_lt_top (ε := 1) one_pos)
  intro v hv
  exact (h1 hv).ge

/- English proof (translation)
Use `haveI := finite_on_compacts h hβ`. Use `haveI := finite_on_compacts h' hβ`. Use `Measure.ext_of_integral_eq_on_compactlySupported_nnreal fun g => ?_` and prove the remaining obligations. Use `set φ : V → ℝ := fun v => (g v : ℝ) with hφdef`. Establish `hφ : Continuous φ` using `NNReal.continuous_coe.comp g.continuous`.

Establish `hc : HasCompactSupport φ` using `HasCompactSupport.comp_left g.hasCompactSupport rfl`. Establish `h0 : ∀ v, 0 ≤ φ v` using `fun v => (g v).2`. Take `⟨hi, hg⟩` from `h.2.2 φ hφ hc (Set.subset_univ _)`. Take `⟨hi', hg'⟩` from `h'.2.2 φ hφ hc (Set.subset_univ _)`. Establish `hφm : Measurable fun v => ENNReal.ofReal (φ v)` using `ENNReal.measurable_ofReal.comp hφ.measurable`.

Establish `c : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) B` using `(ENNReal.continuous_ofReal.comp_continuousOn hg).congr fun b hb => (ofReal_integral_eq_lintegral_ofReal (hi b hb) (Filter.Eventually.of_forall h0)).symm`. Establish `c' : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' b)) B` using `(ENNReal.continuous_ofReal.comp_continuousOn hg').congr fun b hb => (ofReal_integral_eq_lintegral_ofReal (hi' b hb) (Filter.Eventually.of_forall h0)).symm`. Establish `hae : (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) =ᵐ[ν.restrict B] (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' b))`. Use `ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ (c.aemeasurable hB.measurableSet) (c'.aemeasurable hB.measurableSet) fun S hS _ => ?_` and prove the remaining obligations. Rewrite using `[Measure.restrict_restrict hS, ← lintegral_preimage hf h _ hφm _ (hS.inter hB.measurableSet), ← lintegral_preimage hf h' _ hφm _ (hS.inter hB.measurableSet)]`.

Establish `e` using `Measure.eqOn_open_of_ae_eq hae hB c c' hβ`. Simplify using `only at e`. Rewrite `e` using `[← ofReal_integral_eq_lintegral_ofReal (hi β hβ) (Filter.Eventually.of_forall h0), ← ofReal_integral_eq_lintegral_ofReal (hi' β hβ) (Filter.Eventually.of_forall h0)]`. Conclude with `(ENNReal.ofReal_eq_ofReal_iff (integral_nonneg h0) (integral_nonneg h0)).1 e`.
-/
theorem eq_at [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [BorelSpace V]
    [BorelSpace X] [SigmaFinite ν] [ν.IsOpenPosMeasure]
    {fib fib' : X → Measure V} (hf : Measurable f) (hB : IsOpen B)
    (h : IsFibreFamily μ f id Set.univ ν B fib) (h' : IsFibreFamily μ f id Set.univ ν B fib')
    {β : X} (hβ : β ∈ B) : fib β = fib' β := by
  haveI := finite_on_compacts h hβ
  haveI := finite_on_compacts h' hβ
  refine Measure.ext_of_integral_eq_on_compactlySupported_nnreal fun g => ?_
  set φ : V → ℝ := fun v => (g v : ℝ) with hφdef
  have hφ : Continuous φ := NNReal.continuous_coe.comp g.continuous
  have hc : HasCompactSupport φ := HasCompactSupport.comp_left g.hasCompactSupport rfl
  have h0 : ∀ v, 0 ≤ φ v := fun v => (g v).2
  obtain ⟨hi, hg⟩ := h.2.2 φ hφ hc (Set.subset_univ _)
  obtain ⟨hi', hg'⟩ := h'.2.2 φ hφ hc (Set.subset_univ _)
  have hφm : Measurable fun v => ENNReal.ofReal (φ v) :=
    ENNReal.measurable_ofReal.comp hφ.measurable
  have c : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) B :=
    (ENNReal.continuous_ofReal.comp_continuousOn hg).congr fun b hb =>
      (ofReal_integral_eq_lintegral_ofReal (hi b hb) (Filter.Eventually.of_forall h0)).symm
  have c' : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' b)) B :=
    (ENNReal.continuous_ofReal.comp_continuousOn hg').congr fun b hb =>
      (ofReal_integral_eq_lintegral_ofReal (hi' b hb) (Filter.Eventually.of_forall h0)).symm
  have hae : (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) =ᵐ[ν.restrict B]
      (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' b)) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ (c.aemeasurable hB.measurableSet)
      (c'.aemeasurable hB.measurableSet) fun S hS _ => ?_
    rw [Measure.restrict_restrict hS,
      ← lintegral_preimage hf h _ hφm _ (hS.inter hB.measurableSet),
      ← lintegral_preimage hf h' _ hφm _ (hS.inter hB.measurableSet)]
  have e := Measure.eqOn_open_of_ae_eq hae hB c c' hβ
  simp only at e
  rw [← ofReal_integral_eq_lintegral_ofReal (hi β hβ) (Filter.Eventually.of_forall h0),
    ← ofReal_integral_eq_lintegral_ofReal (hi' β hβ) (Filter.Eventually.of_forall h0)] at e
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg h0) (integral_nonneg h0)).1 e

end General

/- English proof (translation)
Establish `h1 : Continuous (Algebra.trace R (R ⊗[F] E))` using `IsModuleTopology.continuous_of_linearMap _`. Establish `h2` using `GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ`. Unfold `qR hR Formalism.UG.hform`. Use `continuous_const.mul (h1.comp ?_)` and prove the remaining obligations. Use `fun_prop`.
-/
theorem continuous_qR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Continuous fun X : Fin 1 → Fin M → R ⊗[F] E => qR R σ J (X 0) := by
  have h1 : Continuous (Algebra.trace R (R ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap _
  have h2 := GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ
  unfold qR hR Formalism.UG.hform
  refine continuous_const.mul (h1.comp ?_)
  fun_prop

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ R _ _ _ _ _ _ _ _ _ hN M J μ ν β m hν hβ hm`. Take `⟨fib, h, rfl⟩` from `hm`. Use `haveI := hN.2.2.1`. Establish `hB : IsOpen {c : R | IsUnit c}` using `(IsOpenUnits.isOpenEmbedding_unitsVal (M := R)).isOpen_range`. Use `⟨?_, finite_on_compacts h hβ, ?_⟩` and prove the remaining obligations.

Use `measure_mono_null ?_ (h.1 β)` and prove the remaining obligations. Introduce `X hX hX'`. Conclude with `hX hX'.1`. Introduce and unpack `m' ⟨fib', h', rfl⟩`. Conclude with `eq_at (continuous_qR σ R J).measurable hB h' h hβ`.
-/
theorem fibAt_basic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure R) (β : R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)), ν.IsAddHaarMeasure → IsUnit β → FibAt R σ J μ ν β m → m {X | qR R σ J (X 0) ≠ β} = 0 ∧ IsFiniteMeasureOnCompacts m ∧ ∀ m', FibAt R σ J μ ν β m' → m' = m := by
  intro F E _ _ _ _ _ σ R _ _ _ _ _ _ _ _ _ hN M J μ ν β m hν hβ hm
  obtain ⟨fib, h, rfl⟩ := hm
  haveI := hN.2.2.1
  have hB : IsOpen {c : R | IsUnit c} :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := R)).isOpen_range
  refine ⟨?_, finite_on_compacts h hβ, ?_⟩
  · refine measure_mono_null ?_ (h.1 β)
    intro X hX hX'
    exact hX hX'.1
  · rintro m' ⟨fib', h', rfl⟩
    exact eq_at (continuous_qR σ R J).measurable hB h' h hβ

end GlobalTheory.GaugeEx.FibBasic

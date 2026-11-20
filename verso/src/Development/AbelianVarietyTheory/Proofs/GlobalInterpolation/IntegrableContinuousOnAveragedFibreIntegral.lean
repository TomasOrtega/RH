import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FibOfZero

open MeasureTheory Topology
open scoped Pointwise

namespace GlobalTheory.QuadFibre

/- English proof (translation)
Take `⟨-, -, -, hmul, hinv, hnorm, -, -⟩` from `h`. Rewrite `ht`, `hy` using `[Set.mem_smul_set]`. Take `⟨a, ha, rfl⟩` from `ht`. Take `⟨b, hb, rfl⟩` from `hy`. Establish `hb0 : b ≠ 0`.

Introduce `hb0`. Use `hnorm b hb` as an intermediate fact. Rewrite `this` using `[hb0, norm_zero]`. Conclude with `zero_ne_one this`. Use `⟨smul_ne_zero h0 hb0, ?_⟩` and prove the remaining obligations.

Simplify using `only [smul_eq_mul]`. Rewrite using `[mul_div_mul_left a b h0, div_eq_mul_inv]`. Conclude with `hmul a ha _ (hinv b hb)`.
-/
theorem IsSqrtOn.div_mem_of_mem_smul {K : Type} [NormedField K] {U : Set K} {s : K → K}
    (h : IsSqrtOn U s) {t₀ t y : K} (h0 : t₀ ≠ 0) (ht : t ∈ t₀ • U) (hy : y ∈ t₀ • U) :
    y ≠ 0 ∧ t / y ∈ U := by
  obtain ⟨-, -, -, hmul, hinv, hnorm, -, -⟩ := h
  rw [Set.mem_smul_set] at ht hy
  obtain ⟨a, ha, rfl⟩ := ht
  obtain ⟨b, hb, rfl⟩ := hy
  have hb0 : b ≠ 0 := by
    intro hb0
    have := hnorm b hb
    rw [hb0, norm_zero] at this
    exact zero_ne_one this
  refine ⟨smul_ne_zero h0 hb0, ?_⟩
  simp only [smul_eq_mul]
  rw [mul_div_mul_left a b h0, div_eq_mul_inv]
  exact hmul a ha _ (hinv b hb)

/- English proof (translation)
Take `⟨-, -, -, hmul, hinv, hnorm, -, -⟩` from `h`. Rewrite `ht` using `[Set.mem_smul_set]`. Take `⟨a, ha, rfl⟩` from `ht`. Establish `ha0 : a ≠ 0`. Introduce `ha0`.

Use `hnorm a ha` as an intermediate fact. Rewrite `this` using `[ha0, norm_zero]`. Conclude with `zero_ne_one this`. Establish `haU : a • U = U`. Use extensionality with `x`.

Rewrite using `[Set.mem_smul_set]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, rfl⟩`. Conclude with `hmul a ha b hb`. Introduce `hx`.

Use `⟨a⁻¹ * x, hmul _ (hinv a ha) x hx, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul]`. Rewrite using `[smul_eq_mul, mul_smul, haU]`.
-/
theorem IsSqrtOn.smul_eq_of_mem_smul {K : Type} [NormedField K] {U : Set K} {s : K → K}
    (h : IsSqrtOn U s) {t₀ t : K} (ht : t ∈ t₀ • U) : t • U = t₀ • U := by
  obtain ⟨-, -, -, hmul, hinv, hnorm, -, -⟩ := h
  rw [Set.mem_smul_set] at ht
  obtain ⟨a, ha, rfl⟩ := ht
  have ha0 : a ≠ 0 := by
    intro ha0
    have := hnorm a ha
    rw [ha0, norm_zero] at this
    exact zero_ne_one this
  have haU : a • U = U := by
    ext x
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hmul a ha b hb
    · intro hx
      refine ⟨a⁻¹ * x, hmul _ (hinv a ha) x hx, ?_⟩
      rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
  rw [smul_eq_mul, mul_smul, haU]

/- English proof (translation)
Take `⟨-, -, -, -, -, hnorm, -, hsq⟩` from `h`. Establish `h2 : ‖s a‖ ^ 2 = 1` using `by rw [← norm_pow, hsq a ha, hnorm a ha]`. Establish `h0` using `norm_nonneg (s a)`. Use polynomial arithmetic with `[sq_nonneg (‖s a‖ - 1)]`.
-/
theorem IsSqrtOn.norm_sqrt {K : Type} [NormedField K] {U : Set K} {s : K → K}
    (h : IsSqrtOn U s) {a : K} (ha : a ∈ U) : ‖s a‖ = 1 := by
  obtain ⟨-, -, -, -, -, hnorm, -, hsq⟩ := h
  have h2 : ‖s a‖ ^ 2 = 1 := by rw [← norm_pow, hsq a ha, hnorm a ha]
  have h0 := norm_nonneg (s a)
  nlinarith [sq_nonneg (‖s a‖ - 1)]

/- English proof (translation)
Take `⟨C, hC⟩` from `hφ.bounded_above_of_compact_support hc`. Establish `hC0 : 0 ≤ C` using `(norm_nonneg _).trans (hC 0)`. Use `set T : Set V := Metric.sphere (0 : K) 1 • tsupport φ with hTdef`. Establish `hT : IsCompact T`. Use `((isCompact_sphere (0 : K) 1).prod hc).image (f := fun p : K × V => p.1 • p.2) continuous_smul` as an intermediate fact.

Rewrite `this` using `[Set.image_smul_prod]`. Then use the resulting hypothesis. Use `⟨T.indicator (fun _ => C), ?_, ?_⟩` and prove the remaining obligations. Conclude with `(integrable_indicator_iff hT.isClosed.measurableSet).mpr (integrableOn_const hT.measure_lt_top.ne)`. Introduce `a x ha`. Distinguish the cases in `hx : φ (a • x) = 0`.

Rewrite using `[hx, norm_zero]`. Conclude with `Set.indicator_nonneg (fun _ _ => hC0) x`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Rewrite `ha` using `[norm_zero]`.

Conclude with `zero_ne_one ha`. Establish `hmem : x ∈ T`. Use `Set.mem_smul.mpr ⟨a⁻¹, ?_, a • x, subset_tsupport _ (Function.mem_support.mpr hx), inv_smul_smul₀ ha0 x⟩` and prove the remaining obligations. Rewrite using `[mem_sphere_zero_iff_norm, norm_inv, ha, inv_one]`. Rewrite using `[Set.indicator_of_mem hmem]`.

Conclude with `hC _`.
-/
theorem exists_integrable_bound_unit_smul {K V : Type} [NormedField K] [ProperSpace K]
    [AddCommGroup V] [Module K V] [TopologicalSpace V] [ContinuousSMul K V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [IsFiniteMeasureOnCompacts μ]
    {φ : V → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    ∃ g : V → ℝ, Integrable g μ ∧ ∀ (a : K) (x : V), ‖a‖ = 1 → ‖φ (a • x)‖ ≤ g x := by
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set T : Set V := Metric.sphere (0 : K) 1 • tsupport φ with hTdef
  have hT : IsCompact T := by
    have := ((isCompact_sphere (0 : K) 1).prod hc).image (f := fun p : K × V => p.1 • p.2) continuous_smul
    rwa [Set.image_smul_prod] at this
  refine ⟨T.indicator (fun _ => C), ?_, ?_⟩
  · exact (integrable_indicator_iff hT.isClosed.measurableSet).mpr
      (integrableOn_const hT.measure_lt_top.ne)
  · intro a x ha
    by_cases hx : φ (a • x) = 0
    · rw [hx, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => hC0) x
    · have ha0 : a ≠ 0 := by
        rintro rfl
        rw [norm_zero] at ha
        exact zero_ne_one ha
      have hmem : x ∈ T := by
        refine Set.mem_smul.mpr ⟨a⁻¹, ?_, a • x, subset_tsupport _ (Function.mem_support.mpr hx),
          inv_smul_smul₀ ha0 x⟩
        rw [mem_sphere_zero_iff_norm, norm_inv, ha, inv_one]
      rw [Set.indicator_of_mem hmem]
      exact hC _

/- English proof (translation)
Establish `h'` using `h`. Take `⟨hUo, -, h1, -, -, -, hs, -⟩` from `h'`. Establish `hmf : ∀ t' : K, Measurable (fun x : V => s (t' / q x) • x)`. Introduce `t'`. Establish `hd : Measurable (fun x : V => t' / q x)`.

Repeatedly rewrite using `[div_eq_mul_inv]`. Conclude with `(hq.measurable.inv).const_mul t'`. Conclude with `(hs.measurable.comp hd).smul measurable_id`. Take `⟨g, hg, hgb⟩` from `exists_integrable_bound_unit_smul (K := K) μ hφ hc`. Establish `hset : ∀ t : K, t ≠ 0 → MeasurableSet (q ⁻¹' (t • U))` using `fun t ht => (hUo.smul₀ ht).measurableSet.preimage hq.measurable`.

Establish `hself : ∀ t : K, t ∈ t • U` using `fun t => by`. Simplify using `using Set.smul_mem_smul_set (a := t) h1`. Establish `hν : ∀ t : K, t ≠ 0 → ν (t • U) ≠ 0` using `fun t ht => ((hUo.smul₀ ht).measure_pos ν ⟨t, hself t⟩).ne'`. Establish `hbd : ∀ t t' : K, t ≠ 0 → t' ∈ t • U → ∀ x ∈ q ⁻¹' (t • U), ‖φ (s (t' / q x) • x)‖ ≤ g x` using `fun t t' ht ht' x hx => hgb _ x (h.norm_sqrt (h.div_mem_of_mem_smul ht ht' hx).2)`. Establish `hint : ∀ t : K, t ≠ 0 → Integrable (fun x => φ (s (t / q x) • x)) (μ.restrict (q ⁻¹' (t • U)))`.

Introduce `t ht`. Use `Integrable.mono' hg.restrict (hφ.measurable.comp (hmf t)).aestronglyMeasurable ?_` and prove the remaining obligations. Conclude with `(ae_restrict_iff' (hset t ht)).mpr (Filter.Eventually.of_forall (fun x hx => hbd t t ht (hself t) x hx))`. Establish `heq : ∀ t : K, t ≠ 0 → ∀ t' ∈ t • U, ∫ x, φ x ∂(fibOf μ ν q U s t') = (ν (t • U))⁻¹.toReal • ∫ x in q ⁻¹' (t • U), φ (s (t' / q x) • x) ∂μ`. Introduce `t ht t' ht'`.

Establish `ht'0 : t' ≠ 0` using `(h.div_mem_of_mem_smul ht ht' ht').1`. Rewrite using `[fibOf_ne μ ν q U s ht'0, h.smul_eq_of_mem_smul ht', integral_smul_measure, integral_map (hmf t').aemeasurable hφ.aestronglyMeasurable]`. Use `⟨fun t ht => ?_, fun t ht => ?_⟩` and prove the remaining obligations. Rewrite using `[fibOf_ne μ ν q U s ht]`. Use `Integrable.smul_measure ?_ (ENNReal.inv_ne_top.mpr (hν t ht))` and prove the remaining obligations.

Conclude with `(integrable_map_measure hφ.aestronglyMeasurable (hmf t).aemeasurable).mpr (hint t ht)`. Establish `ht0 : t ≠ 0` using `ht`. Apply `ContinuousAt.continuousWithinAt` to reduce the goal to its premises. Establish `hnhds : t • U ∈ 𝓝 t` using `(hUo.smul₀ ht0).mem_nhds (hself t)`. Establish `hev : (fun t' => (ν (t • U))⁻¹.toReal • ∫ x in q ⁻¹' (t • U), φ (s (t' / q x) • x) ∂μ) =ᶠ[𝓝 t] (fun t' => ∫ x, φ x ∂(fibOf μ ν q U s t'))` using `Filter.eventually_of_mem hnhds (fun t' ht' => (heq t ht0 t' ht').symm)`.

Use `ContinuousAt.congr (ContinuousAt.const_smul (continuousAt_of_dominated (F := fun t' x => φ (s (t' / q x) • x)) (bound := g) ?_ ?_ hg.restrict ?_) ((ν (t • U))⁻¹.toReal)) hev` and prove the remaining obligations. Conclude with `Filter.Eventually.of_forall (fun t' => (hφ.measurable.comp (hmf t')).aestronglyMeasurable)`. Conclude with `Filter.eventually_of_mem hnhds (fun t' ht' => (ae_restrict_iff' (hset t ht0)).mpr (Filter.Eventually.of_forall (fun x hx => hbd t t' ht0 ht' x hx)))`. Conclude with `Filter.Eventually.of_forall (fun x => (hφ.comp ((hs.comp (continuous_id.div_const _)).smul continuous_const)).continuousAt)`.
-/
theorem integrable_and_continuousOn_fibOf (K V : Type) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V]
    [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure]
    (q : V → K) (hq : Continuous q) (_hh : ∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x)
    (U : Set K) (s : K → K) (h : IsSqrtOn U s) (φ : V → ℝ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) :
    (∀ t : K, t ≠ 0 → Integrable φ (fibOf μ ν q U s t)) ∧
      ContinuousOn (fun t => ∫ x, φ x ∂(fibOf μ ν q U s t)) {t : K | t ≠ 0} := by
  have h' := h
  obtain ⟨hUo, -, h1, -, -, -, hs, -⟩ := h'
  have hmf : ∀ t' : K, Measurable (fun x : V => s (t' / q x) • x) := by
    intro t'
    have hd : Measurable (fun x : V => t' / q x) := by
      simp_rw [div_eq_mul_inv]
      exact (hq.measurable.inv).const_mul t'
    exact (hs.measurable.comp hd).smul measurable_id
  obtain ⟨g, hg, hgb⟩ := exists_integrable_bound_unit_smul (K := K) μ hφ hc
  have hset : ∀ t : K, t ≠ 0 → MeasurableSet (q ⁻¹' (t • U)) := fun t ht =>
    (hUo.smul₀ ht).measurableSet.preimage hq.measurable
  have hself : ∀ t : K, t ∈ t • U := fun t => by
    simpa using Set.smul_mem_smul_set (a := t) h1
  have hν : ∀ t : K, t ≠ 0 → ν (t • U) ≠ 0 := fun t ht =>
    ((hUo.smul₀ ht).measure_pos ν ⟨t, hself t⟩).ne'
  have hbd : ∀ t t' : K, t ≠ 0 → t' ∈ t • U → ∀ x ∈ q ⁻¹' (t • U), ‖φ (s (t' / q x) • x)‖ ≤ g x :=
    fun t t' ht ht' x hx => hgb _ x (h.norm_sqrt (h.div_mem_of_mem_smul ht ht' hx).2)
  have hint : ∀ t : K, t ≠ 0 →
      Integrable (fun x => φ (s (t / q x) • x)) (μ.restrict (q ⁻¹' (t • U))) := by
    intro t ht
    refine Integrable.mono' hg.restrict (hφ.measurable.comp (hmf t)).aestronglyMeasurable ?_
    exact (ae_restrict_iff' (hset t ht)).mpr
      (Filter.Eventually.of_forall (fun x hx => hbd t t ht (hself t) x hx))
  have heq : ∀ t : K, t ≠ 0 → ∀ t' ∈ t • U, ∫ x, φ x ∂(fibOf μ ν q U s t') =
      (ν (t • U))⁻¹.toReal • ∫ x in q ⁻¹' (t • U), φ (s (t' / q x) • x) ∂μ := by
    intro t ht t' ht'
    have ht'0 : t' ≠ 0 := (h.div_mem_of_mem_smul ht ht' ht').1
    rw [fibOf_ne μ ν q U s ht'0, h.smul_eq_of_mem_smul ht', integral_smul_measure,
      integral_map (hmf t').aemeasurable hφ.aestronglyMeasurable]
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · rw [fibOf_ne μ ν q U s ht]
    refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.mpr (hν t ht))
    exact (integrable_map_measure hφ.aestronglyMeasurable (hmf t).aemeasurable).mpr (hint t ht)
  · have ht0 : t ≠ 0 := ht
    apply ContinuousAt.continuousWithinAt
    have hnhds : t • U ∈ 𝓝 t := (hUo.smul₀ ht0).mem_nhds (hself t)
    have hev : (fun t' => (ν (t • U))⁻¹.toReal • ∫ x in q ⁻¹' (t • U), φ (s (t' / q x) • x) ∂μ)
        =ᶠ[𝓝 t] (fun t' => ∫ x, φ x ∂(fibOf μ ν q U s t')) :=
      Filter.eventually_of_mem hnhds (fun t' ht' => (heq t ht0 t' ht').symm)
    refine ContinuousAt.congr (ContinuousAt.const_smul (continuousAt_of_dominated
      (F := fun t' x => φ (s (t' / q x) • x)) (bound := g) ?_ ?_ hg.restrict ?_)
      ((ν (t • U))⁻¹.toReal)) hev
    · exact Filter.Eventually.of_forall
        (fun t' => (hφ.measurable.comp (hmf t')).aestronglyMeasurable)
    · exact Filter.eventually_of_mem hnhds (fun t' ht' => (ae_restrict_iff' (hset t ht0)).mpr
        (Filter.Eventually.of_forall (fun x hx => hbd t t' ht0 ht' x hx)))
    · exact Filter.Eventually.of_forall (fun x =>
        (hφ.comp ((hs.comp (continuous_id.div_const _)).smul continuous_const)).continuousAt)

end GlobalTheory.QuadFibre

import Mathlib
open MeasureTheory Topology

namespace GlobalTheory

/- English proof (translation)
Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hc`. Set `e : V ≃L[K] V` to `ContinuousLinearEquiv.smulLeft (Units.mk0 c hc0)`. Establish `he : (fun x : V => c • x) = e`.

Use extensionality with `x`. Simplify using `[e]`. Use `haveI : (Measure.map (fun x : V => c • x) μ).IsAddHaarMeasure := by`. Rewrite using `[he]`. Conclude with `e.isAddHaarMeasure_map μ`.

Establish `hk` using `Measure.isAddLeftInvariant_eq_smul (Measure.map (fun x : V => c • x) μ) μ`. Use `set k := Measure.addHaarScalarFactor (Measure.map (fun x : V => c • x) μ) μ`. Take `⟨C, hC, hC0⟩` from `exists_compact_mem_nhds (0 : V)`. Set `S : Set V` to `(fun p : K × V => p.1 • p.2) '' (Metric.sphere (0 : K) 1 ×ˢ C)`. Establish `hS : IsCompact S` using `((isCompact_sphere (0 : K) 1).prod hC).image continuous_smul`.

Establish `hCS : C ⊆ S` using `fun x hx => ⟨(1, x), ⟨by simp, hx⟩, by simp⟩`. Establish `hpos : μ S ≠ 0` using `((Measure.measure_pos_of_mem_nhds μ hC0).trans_le (measure_mono hCS)).ne'`. Establish `hfin : μ S ≠ ⊤` using `hS.measure_lt_top.ne`. Establish `hpre : (fun x : V => c • x) ⁻¹' S = S`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨a, y⟩, ⟨ha, hy⟩, h⟩`. Use `⟨(c⁻¹ * a, y), ⟨?_, hy⟩, ?_⟩` and prove the remaining obligations. Simplify using `at ha`. Simplify using `[ha, hc]`.

Simplify using `only at h ⊢`. Rewrite using `[mul_smul, h, smul_smul, inv_mul_cancel₀ hc0, one_smul]`. Introduce and unpack `⟨⟨a, y⟩, ⟨ha, hy⟩, h⟩`. Use `⟨(c * a, y), ⟨?_, hy⟩, ?_⟩` and prove the remaining obligations. Simplify using `at ha`.

Simplify using `[ha, hc]`. Simplify using `only at h ⊢`. Rewrite using `[mul_smul, h]`. Establish `hm : Measure.map (fun x : V => c • x) μ S = μ S`. Rewrite using `[Measure.map_apply (continuous_const_smul c).measurable hS.measurableSet, hpre]`.

Establish `hk1 : k = 1`. Rewrite `hm` using `[hk, Measure.smul_apply]`. Establish `h1 : (k : ENNReal) * μ S = 1 * μ S`. Rewrite using `[one_mul]`. Simplify `hm` using `[ENNReal.smul_def]`.

Use `(ENNReal.mul_left_inj hpos hfin).1 h1` as an intermediate fact. Conclude with `this` after adjusting the coercions. Rewrite using `[hk, hk1, one_smul]`.
-/
theorem addHaar_map_smul_of_norm_eq_one (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (c : K) (hc : ‖c‖ = 1) : Measure.map (fun x : V => c • x) μ = μ := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  let e : V ≃L[K] V := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc0)
  have he : (fun x : V => c • x) = e := by
    ext x
    simp [e]
  haveI : (Measure.map (fun x : V => c • x) μ).IsAddHaarMeasure := by
    rw [he]
    exact e.isAddHaarMeasure_map μ
  have hk := Measure.isAddLeftInvariant_eq_smul (Measure.map (fun x : V => c • x) μ) μ
  set k := Measure.addHaarScalarFactor (Measure.map (fun x : V => c • x) μ) μ
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : V)
  let S : Set V := (fun p : K × V => p.1 • p.2) '' (Metric.sphere (0 : K) 1 ×ˢ C)
  have hS : IsCompact S :=
    ((isCompact_sphere (0 : K) 1).prod hC).image continuous_smul
  have hCS : C ⊆ S := fun x hx => ⟨(1, x), ⟨by simp, hx⟩, by simp⟩
  have hpos : μ S ≠ 0 :=
    ((Measure.measure_pos_of_mem_nhds μ hC0).trans_le (measure_mono hCS)).ne'
  have hfin : μ S ≠ ⊤ := hS.measure_lt_top.ne
  have hpre : (fun x : V => c • x) ⁻¹' S = S := by
    ext x
    constructor
    · rintro ⟨⟨a, y⟩, ⟨ha, hy⟩, h⟩
      refine ⟨(c⁻¹ * a, y), ⟨?_, hy⟩, ?_⟩
      · simp at ha
        simp [ha, hc]
      · simp only at h ⊢
        rw [mul_smul, h, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    · rintro ⟨⟨a, y⟩, ⟨ha, hy⟩, h⟩
      refine ⟨(c * a, y), ⟨?_, hy⟩, ?_⟩
      · simp at ha
        simp [ha, hc]
      · simp only at h ⊢
        rw [mul_smul, h]
  have hm : Measure.map (fun x : V => c • x) μ S = μ S := by
    rw [Measure.map_apply (continuous_const_smul c).measurable hS.measurableSet, hpre]
  have hk1 : k = 1 := by
    rw [hk, Measure.smul_apply] at hm
    have h1 : (k : ENNReal) * μ S = 1 * μ S := by
      rw [one_mul]
      simpa [ENNReal.smul_def] using hm
    have := (ENNReal.mul_left_inj hpos hfin).1 h1
    exact_mod_cast this
  rw [hk, hk1, one_smul]

end GlobalTheory

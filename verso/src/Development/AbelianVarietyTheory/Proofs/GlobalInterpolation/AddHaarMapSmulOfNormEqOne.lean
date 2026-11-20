import Mathlib
open MeasureTheory Topology

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Introduce a local definition for the expression. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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

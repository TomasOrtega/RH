import Mathlib

open MeasureTheory
open scoped Pointwise NNReal ENNReal

namespace GlobalTheory

/- English proof (translation)
Establish `h` using `Measure.isMulLeftInvariant_eq_smul (Measure.map (fun g => g * k) μ) μ`. Use `set c := Measure.haarScalarFactor (Measure.map (fun g => g * k) μ) μ with hc`. Take `⟨C, hC, hC1⟩` from `exists_compact_mem_nhds (1 : G)`. Establish `hS : IsCompact (C * (K : Set G))` using `hC.mul hK`. Establish `hsub : C ⊆ C * (K : Set G)` using `fun x hx => ⟨x, hx, 1, K.one_mem, mul_one x⟩`.

Establish `hpos : 0 < μ (C * (K : Set G))` using `Measure.measure_pos_of_mem_nhds μ (Filter.mem_of_superset hC1 hsub)`. Establish `hfin : μ (C * (K : Set G)) < ⊤` using `hS.measure_lt_top`. Establish `hpre : (fun g => g * k) ⁻¹' (C * (K : Set G)) = C * (K : Set G)`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, ha, b, hb, hab⟩`. Use `⟨a, ha, b * k⁻¹, K.mul_mem hb (K.inv_mem hk), ?_⟩` and prove the remaining obligations. Simplify using `only at hab ⊢`. Rewrite using `[← mul_assoc, hab, mul_inv_cancel_right]`. Introduce and unpack `⟨a, ha, b, hb, rfl⟩`.

Conclude with `⟨a, ha, b * k, K.mul_mem hb hk, (mul_assoc _ _ _).symm⟩`. Establish `h1 : Measure.map (fun g => g * k) μ (C * (K : Set G)) = μ (C * (K : Set G))`. Use `(MeasurableEquiv.mulRight k).map_apply (μ := μ) (C * (K : Set G))` as an intermediate fact. Rewrite `this` using `[MeasurableEquiv.coe_mulRight, hpre]`. Conclude with `this`.

Establish `h2 : (c : ℝ≥0∞) * μ (C * (K : Set G)) = 1 * μ (C * (K : Set G))`. Rewrite using `[one_mul]`. Use `conv_rhs => rw [← h1, h]`. Simplify using the standard rewrite rules. Establish `h3 : (c : ℝ≥0∞) = 1` using `(ENNReal.mul_left_inj hpos.ne' hfin.ne).1 h2`.

Establish `h4 : c = 1` using `by exact_mod_cast h3`. Rewrite using `[h, h4, one_smul]`.
-/
theorem haar_map_mul_right_of_mem_compact_subgroup {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Subgroup G) (hK : IsCompact (K : Set G))
    (k : G) (hk : k ∈ K) : Measure.map (fun g => g * k) μ = μ := by
  have h := Measure.isMulLeftInvariant_eq_smul (Measure.map (fun g => g * k) μ) μ
  set c := Measure.haarScalarFactor (Measure.map (fun g => g * k) μ) μ with hc
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : G)
  have hS : IsCompact (C * (K : Set G)) := hC.mul hK
  have hsub : C ⊆ C * (K : Set G) := fun x hx => ⟨x, hx, 1, K.one_mem, mul_one x⟩
  have hpos : 0 < μ (C * (K : Set G)) :=
    Measure.measure_pos_of_mem_nhds μ (Filter.mem_of_superset hC1 hsub)
  have hfin : μ (C * (K : Set G)) < ⊤ := hS.measure_lt_top
  have hpre : (fun g => g * k) ⁻¹' (C * (K : Set G)) = C * (K : Set G) := by
    ext x
    constructor
    · rintro ⟨a, ha, b, hb, hab⟩
      refine ⟨a, ha, b * k⁻¹, K.mul_mem hb (K.inv_mem hk), ?_⟩
      simp only at hab ⊢
      rw [← mul_assoc, hab, mul_inv_cancel_right]
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b * k, K.mul_mem hb hk, (mul_assoc _ _ _).symm⟩
  have h1 : Measure.map (fun g => g * k) μ (C * (K : Set G)) = μ (C * (K : Set G)) := by
    have := (MeasurableEquiv.mulRight k).map_apply (μ := μ) (C * (K : Set G))
    rw [MeasurableEquiv.coe_mulRight, hpre] at this
    exact this
  have h2 : (c : ℝ≥0∞) * μ (C * (K : Set G)) = 1 * μ (C * (K : Set G)) := by
    rw [one_mul]
    conv_rhs => rw [← h1, h]
    simp
  have h3 : (c : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hpos.ne' hfin.ne).1 h2
  have h4 : c = 1 := by exact_mod_cast h3
  rw [h, h4, one_smul]

end GlobalTheory

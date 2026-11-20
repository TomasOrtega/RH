import Mathlib
open MeasureTheory Pointwise

namespace GlobalTheory

/- English proof (translation)
Introduce `H _ _ _ _ _ _ _ _ μ hμ K hK`. Take `⟨C, hCc, hC1⟩` from `exists_compact_mem_nhds (1 : H)`. Establish `hCm : MeasurableSet C` using `hCc.isClosed.measurableSet`. Establish `hC0 : μ C ≠ 0` using `(Measure.measure_pos_of_mem_nhds μ hC1).ne'`. Establish `hCt : μ C ≠ ⊤` using `hCc.measure_lt_top.ne`.

Establish `hLc : IsCompact (C * K⁻¹)` using `hCc.mul hK.inv`. Establish `hLt : μ (C * K⁻¹) ≠ ⊤` using `hLc.measure_lt_top.ne`. Establish `hpre : ∀ y : H, μ ((· * y) ⁻¹' C) = (Measure.modularCharacterFun y : ENNReal) * μ C`. Introduce `y`. Rewrite using `[← Measure.map_apply (measurable_mul_const y) hCm, Measure.map_right_mul_eq_modularCharacterFun_smul μ y]`.

Rewrite using `[Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]`. Establish `hbound : ∀ y ∈ K, Measure.modularCharacterFun y ≤ (μ (C * K⁻¹)).toNNReal / (μ C).toNNReal`. Introduce `y hy`. Establish `hsub : (· * y) ⁻¹' C ⊆ (C * K⁻¹)`. Introduce `z hz`.

Conclude with `⟨z * y, hz, y⁻¹, by simpa using hy, by simp⟩`. Establish `h1 : (Measure.modularCharacterFun y : ENNReal) * μ C ≤ μ (C * K⁻¹)` using `(hpre y) ▸ measure_mono hsub`. Establish `hCpos : 0 < (μ C).toNNReal` using `ENNReal.toNNReal_pos hC0 hCt`. Rewrite using `[le_div_iff₀ hCpos]`. Use `ENNReal.toNNReal_mono hLt h1` as an intermediate fact.

Simplify `this` using `[ENNReal.toNNReal_mul]`. Use `⟨(μ (C * K⁻¹)).toNNReal / (μ C).toNNReal, fun φ hφ hsupp => ?_⟩` and prove the remaining obligations. Establish `key : ∫⁻ x, φ x ∂μ = ∫⁻ x, (Measure.modularCharacterFun x : ENNReal) * φ x⁻¹ ∂μ`. Establish `h` using `measure_mul_lintegral_eq μ μ hCm φ hφ`. Rewrite `h` using `[hpre, mul_comm _ (μ C), mul_assoc]`.

Rewrite `h` using `[lintegral_const_mul' _ _ hCt]`. Conclude with `(ENNReal.mul_right_inj hC0 hCt).1 h`. Rewrite using `[key, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]`. Use `lintegral_mono fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x⁻¹ ∈ K`.

Establish `hb` using `hbound _ hx`. Establish `hmul : (Measure.modularCharacterFun x⁻¹ : ENNReal) * Measure.modularCharacterFun x = 1`. Rewrite using `[← ENNReal.coe_mul, ← Measure.modularCharacterFun_map_mul, inv_mul_cancel, Measure.modularCharacterFun_map_one, ENNReal.coe_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hsupp _ hx]`.

Conclude with `bot_le`.
-/
theorem lintegral_inv_le_of_support_compact : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ K : Set H, IsCompact K → ∃ B : NNReal, ∀ φ : H → ENNReal, Measurable φ → (∀ x ∉ K, φ x = 0) → ∫⁻ x, φ x⁻¹ ∂μ ≤ B * ∫⁻ x, φ x ∂μ := by
  intro H _ _ _ _ _ _ _ _ μ hμ K hK
  obtain ⟨C, hCc, hC1⟩ := exists_compact_mem_nhds (1 : H)
  have hCm : MeasurableSet C := hCc.isClosed.measurableSet
  have hC0 : μ C ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hC1).ne'
  have hCt : μ C ≠ ⊤ := hCc.measure_lt_top.ne
  have hLc : IsCompact (C * K⁻¹) := hCc.mul hK.inv
  have hLt : μ (C * K⁻¹) ≠ ⊤ := hLc.measure_lt_top.ne
  have hpre : ∀ y : H, μ ((· * y) ⁻¹' C) = (Measure.modularCharacterFun y : ENNReal) * μ C := by
    intro y
    rw [← Measure.map_apply (measurable_mul_const y) hCm,
      Measure.map_right_mul_eq_modularCharacterFun_smul μ y]
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hbound : ∀ y ∈ K, Measure.modularCharacterFun y ≤ (μ (C * K⁻¹)).toNNReal / (μ C).toNNReal := by
    intro y hy
    have hsub : (· * y) ⁻¹' C ⊆ (C * K⁻¹) := by
      intro z hz
      exact ⟨z * y, hz, y⁻¹, by simpa using hy, by simp⟩
    have h1 : (Measure.modularCharacterFun y : ENNReal) * μ C ≤ μ (C * K⁻¹) := (hpre y) ▸ measure_mono hsub
    have hCpos : 0 < (μ C).toNNReal := ENNReal.toNNReal_pos hC0 hCt
    rw [le_div_iff₀ hCpos]
    have := ENNReal.toNNReal_mono hLt h1
    simpa [ENNReal.toNNReal_mul] using this
  refine ⟨(μ (C * K⁻¹)).toNNReal / (μ C).toNNReal, fun φ hφ hsupp => ?_⟩
  have key : ∫⁻ x, φ x ∂μ = ∫⁻ x, (Measure.modularCharacterFun x : ENNReal) * φ x⁻¹ ∂μ := by
    have h := measure_mul_lintegral_eq μ μ hCm φ hφ
    simp_rw [hpre, mul_comm _ (μ C), mul_assoc] at h
    rw [lintegral_const_mul' _ _ hCt] at h
    exact (ENNReal.mul_right_inj hC0 hCt).1 h
  rw [key, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_mono fun x => ?_
  by_cases hx : x⁻¹ ∈ K
  · have hb := hbound _ hx
    have hmul : (Measure.modularCharacterFun x⁻¹ : ENNReal) * Measure.modularCharacterFun x = 1 := by
      rw [← ENNReal.coe_mul, ← Measure.modularCharacterFun_map_mul, inv_mul_cancel,
        Measure.modularCharacterFun_map_one, ENNReal.coe_one]
    calc φ x⁻¹ = ((Measure.modularCharacterFun x⁻¹ : ENNReal) * Measure.modularCharacterFun x) * φ x⁻¹ := by rw [hmul, one_mul]
      _ = (Measure.modularCharacterFun x⁻¹ : ENNReal) * ((Measure.modularCharacterFun x : ENNReal) * φ x⁻¹) := by ring
      _ ≤ _ := by gcongr
  · rw [hsupp _ hx]; exact bot_le

end GlobalTheory

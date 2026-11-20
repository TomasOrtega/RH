import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientMeasureUniqueness.QmuWeight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientMeasureUniqueness.QLiftIsMulLeftInvariant

noncomputable section

open MeasureTheory Pointwise
open scoped ENNReal

namespace PI.QuotMeasUniqW

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ H hH ν hν`. Take `⟨K, hK, hK1⟩` from `exists_compact_mem_nhds (1 : G)`. Establish `hVo : IsOpen (interior K)` using `isOpen_interior`. Establish `hVK : interior K ⊆ K` using `interior_subset`. Establish `h1V : (1 : G) ∈ interior K` using `mem_interior_iff_mem_nhds.2 hK1`.

Take `⟨d, hd⟩` from `TopologicalSpace.exists_dense_seq G`. Establish `hCo : ∀ n, IsOpen (d n • interior K)` using `fun n => hVo.smul (d n)`. Establish `hCm : ∀ n, MeasurableSet (d n • interior K)` using `fun n => (hCo n).measurableSet`. Establish `hind : ∀ n, Measurable ((d n • interior K).indicator (1 : G → ℝ≥0∞))` using `fun n => measurable_one.indicator (hCm n)`. Use `⟨fun x => ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * (d n • interior K).indicator 1 x, Measurable.ennreal_tsum fun n => (hind n).const_mul _, fun g => ?_⟩` and prove the remaining obligations.

Establish `hmg : ∀ n, Measurable fun h : H => (d n • interior K).indicator (1 : G → ℝ≥0∞) (g * (h : G))` using `fun n => (hind n).comp ((measurable_const_mul g).comp measurable_subtype_coe)`. Establish `hterm : ∀ n, Measurable fun h : H => (2⁻¹ : ℝ≥0∞) ^ n * (d n • interior K).indicator 1 (g * (h : G))` using `fun n => (hmg n).const_mul _`. Establish `hM : ν {h : H | (h : G) ∈ K⁻¹ * K} ≠ ⊤`. Establish `hc : IsCompact (((↑) : H → G) ⁻¹' (K⁻¹ * K))` using `hH.isClosedEmbedding_subtypeVal.isCompact_preimage (hK.inv.mul hK)`. Conclude with `hc.measure_lt_top.ne`.

Establish `hle : ∀ n, ∫⁻ h, (d n • interior K).indicator 1 (g * (h : G)) ∂ν ≤ ν {h : H | (h : G) ∈ K⁻¹ * K}`. Introduce `n`. Use `hAvg_indicator_le ν (d n • interior K) K (d n) g ?_` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]`.

Conclude with `hVK hx`. Use `show (∫⁻ h, ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * (d n • interior K).indicator 1 (g * (h : G)) ∂ν) ≠ 0 ∧ (∫⁻ h, ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * (d n • interior K).indicator 1 (g * (h : G)) ∂ν) ≠ ⊤`. Prove the components needed by the constructor for the conclusion. Choose the witnesses or unpack the hypotheses as in `⟨n, hn⟩ : ∃ n, (d n)⁻¹ * g ∈ interior K := by`. Establish `ho : IsOpen {x : G | x⁻¹ * g ∈ interior K}` using `hVo.preimage (continuous_inv.mul continuous_const)`.

Conclude with `hd.exists_mem_open ho ⟨g, by simpa using h1V⟩`. Establish `hSo : IsOpen {h : H | g * (h : G) ∈ d n • interior K}` using `(hCo n).preimage (continuous_const.mul continuous_subtype_val)`. Establish `hS1 : (1 : H) ∈ {h : H | g * (h : G) ∈ d n • interior K}` using `by show g * ((1 : H) : G) ∈ d n • interior K`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]`. Simplify `hn` using `[mul_assoc]`.

Establish `hpos : 0 < ν {h : H | g * (h : G) ∈ d n • interior K}` using `hSo.measure_pos ν ⟨1, hS1⟩`. Establish `heq : ∫⁻ h, (d n • interior K).indicator 1 (g * (h : G)) ∂ν = ν {h : H | g * (h : G) ∈ d n • interior K}`. Establish `hfun : (fun h : H => (d n • interior K).indicator (1 : G → ℝ≥0∞) (g * (h : G))) = ((fun h : H => g * (h : G)) ⁻¹' (d n • interior K)).indicator 1`. Use function extensionality and compare the values at `h`. Conclude with `(indicator_preimage_one (fun h : H => g * (h : G)) (d n • interior K) h).symm`.

Rewrite using `[hfun]`. Conclude with `lintegral_indicator_one hSo.measurableSet`. Apply `ne_of_gt` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lintegral_const_mul _ (hmg n), heq]`.

Use `_ ≤ ∫⁻ h, ∑' m, (2⁻¹ : ℝ≥0∞) ^ m * (d m • interior K).indicator 1 (g * (h : G)) ∂ν := lintegral_mono fun h => ENNReal.le_tsum (f := fun m => (2⁻¹ : ℝ≥0∞) ^ m * (d m • interior K).indicator 1 (g * (h : G))) n`. Rewrite using `[lintegral_tsum fun n => (hterm n).aemeasurable]`. Use `ne_top_of_le_ne_top (b := ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * ν {h : H | (h : G) ∈ K⁻¹ * K}) ?_ ?_` and prove the remaining obligations. Rewrite using `[ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]`. Conclude with `ENNReal.mul_ne_top (by simp) hM`.

Use `ENNReal.tsum_le_tsum fun n => ?_` and prove the remaining obligations. Rewrite using `[lintegral_const_mul _ (hmg n)]`. Use `gcongr`. Conclude with `hle n`.
-/
theorem qmuWeight : QmuWeight := by
  intro G _ _ _ _ _ _ _ _ H hH ν hν
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hVo : IsOpen (interior K) := isOpen_interior
  have hVK : interior K ⊆ K := interior_subset
  have h1V : (1 : G) ∈ interior K := mem_interior_iff_mem_nhds.2 hK1
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq G
  have hCo : ∀ n, IsOpen (d n • interior K) := fun n => hVo.smul (d n)
  have hCm : ∀ n, MeasurableSet (d n • interior K) := fun n => (hCo n).measurableSet
  have hind : ∀ n, Measurable ((d n • interior K).indicator (1 : G → ℝ≥0∞)) :=
    fun n => measurable_one.indicator (hCm n)
  refine ⟨fun x => ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * (d n • interior K).indicator 1 x,
    Measurable.ennreal_tsum fun n => (hind n).const_mul _, fun g => ?_⟩
  have hmg : ∀ n, Measurable fun h : H => (d n • interior K).indicator (1 : G → ℝ≥0∞) (g * (h : G)) :=
    fun n => (hind n).comp ((measurable_const_mul g).comp measurable_subtype_coe)
  have hterm : ∀ n, Measurable fun h : H =>
      (2⁻¹ : ℝ≥0∞) ^ n * (d n • interior K).indicator 1 (g * (h : G)) :=
    fun n => (hmg n).const_mul _
  have hM : ν {h : H | (h : G) ∈ K⁻¹ * K} ≠ ⊤ := by
    have hc : IsCompact (((↑) : H → G) ⁻¹' (K⁻¹ * K)) :=
      hH.isClosedEmbedding_subtypeVal.isCompact_preimage (hK.inv.mul hK)
    exact hc.measure_lt_top.ne
  have hle : ∀ n, ∫⁻ h, (d n • interior K).indicator 1 (g * (h : G)) ∂ν
      ≤ ν {h : H | (h : G) ∈ K⁻¹ * K} := by
    intro n
    refine hAvg_indicator_le ν (d n • interior K) K (d n) g ?_
    intro x hx
    rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul] at hx
    exact hVK hx
  show (∫⁻ h, ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * (d n • interior K).indicator 1 (g * (h : G)) ∂ν) ≠ 0 ∧
    (∫⁻ h, ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * (d n • interior K).indicator 1 (g * (h : G)) ∂ν) ≠ ⊤
  constructor
  · obtain ⟨n, hn⟩ : ∃ n, (d n)⁻¹ * g ∈ interior K := by
      have ho : IsOpen {x : G | x⁻¹ * g ∈ interior K} :=
        hVo.preimage (continuous_inv.mul continuous_const)
      exact hd.exists_mem_open ho ⟨g, by simpa using h1V⟩
    have hSo : IsOpen {h : H | g * (h : G) ∈ d n • interior K} :=
      (hCo n).preimage (continuous_const.mul continuous_subtype_val)
    have hS1 : (1 : H) ∈ {h : H | g * (h : G) ∈ d n • interior K} := by
      show g * ((1 : H) : G) ∈ d n • interior K
      rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
      simpa [mul_assoc] using hn
    have hpos : 0 < ν {h : H | g * (h : G) ∈ d n • interior K} := hSo.measure_pos ν ⟨1, hS1⟩
    have heq : ∫⁻ h, (d n • interior K).indicator 1 (g * (h : G)) ∂ν
        = ν {h : H | g * (h : G) ∈ d n • interior K} := by
      have hfun : (fun h : H => (d n • interior K).indicator (1 : G → ℝ≥0∞) (g * (h : G)))
          = ((fun h : H => g * (h : G)) ⁻¹' (d n • interior K)).indicator 1 := by
        funext h
        exact (indicator_preimage_one (fun h : H => g * (h : G)) (d n • interior K) h).symm
      rw [hfun]
      exact lintegral_indicator_one hSo.measurableSet
    apply ne_of_gt
    calc (0 : ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) ^ n * ν {h : H | g * (h : G) ∈ d n • interior K} :=
          ENNReal.mul_pos (pow_ne_zero _ (by simp)) hpos.ne'
      _ = ∫⁻ h, (2⁻¹ : ℝ≥0∞) ^ n * (d n • interior K).indicator 1 (g * (h : G)) ∂ν := by
          rw [lintegral_const_mul _ (hmg n), heq]
      _ ≤ ∫⁻ h, ∑' m, (2⁻¹ : ℝ≥0∞) ^ m * (d m • interior K).indicator 1 (g * (h : G)) ∂ν :=
          lintegral_mono fun h => ENNReal.le_tsum
            (f := fun m => (2⁻¹ : ℝ≥0∞) ^ m * (d m • interior K).indicator 1 (g * (h : G))) n
  · rw [lintegral_tsum fun n => (hterm n).aemeasurable]
    refine ne_top_of_le_ne_top (b := ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * ν {h : H | (h : G) ∈ K⁻¹ * K}) ?_ ?_
    · rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
      exact ENNReal.mul_ne_top (by simp) hM
    · refine ENNReal.tsum_le_tsum fun n => ?_
      rw [lintegral_const_mul _ (hmg n)]
      gcongr
      exact hle n

end PI.QuotMeasUniqW

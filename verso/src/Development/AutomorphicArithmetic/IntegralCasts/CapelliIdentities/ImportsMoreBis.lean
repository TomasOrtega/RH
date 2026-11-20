import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

/- English proof (translation)
Introduce `G Y _ _ _ _ μ hP b hb S hS hc`. Establish `hB : Measurable fun y => ENNReal.ofReal (b y)` using `hb.meas.ennreal_ofReal`. Establish `hF : ∀ g : G, Measurable (S.indicator fun y => ENNReal.ofReal (b (g⁻¹ • y)))` using `fun g => (hB.comp (hP g⁻¹).measurable).indicator hS`. Establish `hone : ∀ y, ∑' g : G, ENNReal.ofReal (b (g⁻¹ • y)) = 1`. Introduce `y`.

Establish `h : ∑' g : G, ENNReal.ofReal (b (g⁻¹ • y)) = ∑' g : G, ENNReal.ofReal (b (g • y))` using `(Equiv.inv G).tsum_eq (fun g : G => ENNReal.ofReal (b (g • y)))`. Rewrite using `[h, ← ENNReal.ofReal_tsum_of_nonneg (fun g => hb.nonneg _) (hb.sum y).summable, (hb.sum y).tsum_eq, ENNReal.ofReal_one]`. Combine the equalities or inequalities in the displayed calculation. Use `MeasureTheory.lintegral_mono fun y => ?_` and prove the remaining obligations. Take `⟨g, hg⟩` from `hc y`.

Use `le_trans ?_ (ENNReal.le_tsum g)` and prove the remaining obligations. Rewrite using `[Set.indicator_of_mem hg, inv_smul_smul]`. Use `_ = ∑' g : G, ∫⁻ y, S.indicator (fun y => ENNReal.ofReal (b (g⁻¹ • y))) (g • y) ∂μ := MeasureTheory.lintegral_tsum fun g => ((hF g).comp (hP g).measurable).aemeasurable`. Use `_ = ∑' g : G, ∫⁻ y, S.indicator (fun y => ENNReal.ofReal (b (g⁻¹ • y))) y ∂μ := tsum_congr fun g => (hP g).lintegral_comp (hF g)`. Use `_ = ∫⁻ y, ∑' g : G, S.indicator (fun y => ENNReal.ofReal (b (g⁻¹ • y))) y ∂μ := (MeasureTheory.lintegral_tsum fun g => (hF g).aemeasurable).symm`.

Use `_ = ∫⁻ y, S.indicator 1 y ∂μ := by`. Use `MeasureTheory.lintegral_congr fun y => ?_` and prove the remaining obligations. Distinguish the cases in `hy : y ∈ S`. Simplify using `only [Set.indicator_of_mem hy, hone, Pi.one_apply]`. Simplify using `only [Set.indicator_of_notMem hy, tsum_zero]`.

Use `_ = μ S := MeasureTheory.lintegral_indicator_one hS`.
-/
theorem UpperTheory.Reformulated.B.Qf46.cover :
    ∀ {G Y : Type} [inst : Group G] [Countable G] [inst_2 : MeasurableSpace Y] [inst_3 : MulAction G Y]
      (μ : MeasureTheory.Measure Y),
      UpperTheory.Esk.Pres G μ →
        ∀ (b : Y → ℝ),
          UpperTheory.Esk.IsCut G b →
            ∀ (S : Set Y),
              MeasurableSet S →
                (∀ (y : Y), ∃ (g : G), g • y ∈ S) → ∫⁻ (y : Y), ENNReal.ofReal (b y) ∂μ ≤ (μ : Set Y → ENNReal) S := by
  intro G Y _ _ _ _ μ hP b hb S hS hc
  have hB : Measurable fun y => ENNReal.ofReal (b y) := hb.meas.ennreal_ofReal
  have hF : ∀ g : G, Measurable (S.indicator fun y => ENNReal.ofReal (b (g⁻¹ • y))) :=
    fun g => (hB.comp (hP g⁻¹).measurable).indicator hS
  have hone : ∀ y, ∑' g : G, ENNReal.ofReal (b (g⁻¹ • y)) = 1 := by
    intro y
    have h : ∑' g : G, ENNReal.ofReal (b (g⁻¹ • y)) = ∑' g : G, ENNReal.ofReal (b (g • y)) :=
      (Equiv.inv G).tsum_eq (fun g : G => ENNReal.ofReal (b (g • y)))
    rw [h, ← ENNReal.ofReal_tsum_of_nonneg (fun g => hb.nonneg _) (hb.sum y).summable, (hb.sum y).tsum_eq,
      ENNReal.ofReal_one]
  calc ∫⁻ y, ENNReal.ofReal (b y) ∂μ
      ≤ ∫⁻ y, ∑' g : G, S.indicator (fun y => ENNReal.ofReal (b (g⁻¹ • y))) (g • y) ∂μ := by
        refine MeasureTheory.lintegral_mono fun y => ?_
        obtain ⟨g, hg⟩ := hc y
        refine le_trans ?_ (ENNReal.le_tsum g)
        rw [Set.indicator_of_mem hg, inv_smul_smul]
    _ = ∑' g : G, ∫⁻ y, S.indicator (fun y => ENNReal.ofReal (b (g⁻¹ • y))) (g • y) ∂μ :=
        MeasureTheory.lintegral_tsum fun g => ((hF g).comp (hP g).measurable).aemeasurable
    _ = ∑' g : G, ∫⁻ y, S.indicator (fun y => ENNReal.ofReal (b (g⁻¹ • y))) y ∂μ :=
        tsum_congr fun g => (hP g).lintegral_comp (hF g)
    _ = ∫⁻ y, ∑' g : G, S.indicator (fun y => ENNReal.ofReal (b (g⁻¹ • y))) y ∂μ :=
        (MeasureTheory.lintegral_tsum fun g => (hF g).aemeasurable).symm
    _ = ∫⁻ y, S.indicator 1 y ∂μ := by
        refine MeasureTheory.lintegral_congr fun y => ?_
        by_cases hy : y ∈ S
        · simp only [Set.indicator_of_mem hy, hone, Pi.one_apply]
        · simp only [Set.indicator_of_notMem hy, tsum_zero]
    _ = μ S := MeasureTheory.lintegral_indicator_one hS

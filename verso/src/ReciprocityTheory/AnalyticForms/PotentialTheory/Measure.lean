import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]

def chartPartMeasure (A : FinHolAtlas e X) (P : ChartPartition A) (Φ : Fin e → LocPot X)
    (s : ℝ) (j : Fin A.n) : Measure X :=
  ((volume.restrict (A.chart j).target).withDensity fun y =>
    ENNReal.ofReal (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))).map (A.chart j).symm

/- English proof (translation)
Establish `hK : IsCompact (tsupport (P.χ j))` using `(isClosed_tsupport _).isCompact`. Establish `hsrc` using `P.tsupport_subset j`. Use `⟨hK.image_of_continuousOn ((A.chart j).continuousOn.mono hsrc), ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `(A.chart j).map_source (hsrc hx)`.

Introduce `y hy hy'`. Apply `image_eq_zero_of_notMem_tsupport` to reduce the goal to its premises. Introduce `h`. Conclude with `hy' ⟨_, h, (A.chart j).right_inv hy⟩`.
-/
theorem chart_weight_compact [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (P : ChartPartition A) (Φ : Fin e → LocPot X) (j : Fin A.n) :
    IsCompact ((A.chart j) '' tsupport (P.χ j)) ∧
      (A.chart j) '' tsupport (P.χ j) ⊆ (A.chart j).target ∧
      ∀ y ∈ (A.chart j).target, y ∉ (A.chart j) '' tsupport (P.χ j) →
        P.χ j ((A.chart j).symm y) = 0 := by
  have hK : IsCompact (tsupport (P.χ j)) := (isClosed_tsupport _).isCompact
  have hsrc := P.tsupport_subset j
  refine ⟨hK.image_of_continuousOn ((A.chart j).continuousOn.mono hsrc), ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (A.chart j).map_source (hsrc hx)
  · intro y hy hy'
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hy' ⟨_, h, (A.chart j).right_inv hy⟩

/- English proof (translation)
Establish `h` using `((P.smooth j) j).continuousOn`. Rewrite `h` using `[Set.preimage_univ, Set.inter_univ]`. Conclude with `h`.
-/
private theorem chiCont (A : FinHolAtlas e X) (P : ChartPartition A) (j : Fin A.n) :
    ContinuousOn (fun y => P.χ j ((A.chart j).symm y)) (A.chart j).target := by
  have h := ((P.smooth j) j).continuousOn
  rw [Set.preimage_univ, Set.inter_univ] at h
  exact h

/- English proof (translation)
Take `⟨hC, hCT, hz⟩` from `chart_weight_compact A P Φ j`. Establish `hw : ContinuousOn (fun y => s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) (A.chart j).target` using `continuousOn_const.mul ((chiCont A P j).mul (locDensCont A Φ hΦ j))`. Establish `hi : IntegrableOn (fun y => s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) (A.chart j).target`. Use `IntegrableOn.of_forall_diff_eq_zero ((hw.mono hCT).integrableOn_compact hC) (A.chart j).open_target.measurableSet ?_` and prove the remaining obligations. Introduce `y hy`.

Simplify using `[hz y hy.1 hy.2]`. Unfold `chartPartMeasure`. Use `haveI : IsFiniteMeasure ((volume.restrict (A.chart j).target).withDensity fun y => ENNReal.ofReal (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))) := isFiniteMeasure_withDensity_ofReal hi.2`. Use `infer_instance`.
-/
theorem isFiniteMeasure_chartPartMeasure [CompactSpace X] [T2Space X] [BorelSpace X]
    (A : FinHolAtlas e X) (P : ChartPartition A) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (s : ℝ) (j : Fin A.n) :
    IsFiniteMeasure (chartPartMeasure A P Φ s j) := by
  obtain ⟨hC, hCT, hz⟩ := chart_weight_compact A P Φ j
  have hw : ContinuousOn (fun y => s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))
      (A.chart j).target :=
    continuousOn_const.mul ((chiCont A P j).mul (locDensCont A Φ hΦ j))
  have hi : IntegrableOn (fun y => s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))
      (A.chart j).target := by
    refine IntegrableOn.of_forall_diff_eq_zero ((hw.mono hCT).integrableOn_compact hC)
      (A.chart j).open_target.measurableSet ?_
    intro y hy
    simp [hz y hy.1 hy.2]
  unfold chartPartMeasure
  haveI : IsFiniteMeasure ((volume.restrict (A.chart j).target).withDensity fun y =>
      ENNReal.ofReal (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))) :=
    isFiniteMeasure_withDensity_ofReal hi.2
  infer_instance

/- English proof (translation)
Take `⟨hC, hCT, hz⟩` from `chart_weight_compact A P Φ j`. Establish `hL` using `hgi j _ hCT hC`. Establish `hw : ContinuousOn (fun y => s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) (A.chart j).target` using `continuousOn_const.mul ((chiCont A P j).mul (locDensCont A Φ hΦ j))`. Establish `hcont : ContinuousOn (fun y => max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0) (A.chart j).target` using `fun y hy => (hw y hy).max continuousWithinAt_const`. Establish `hsymm : AEMeasurable (fun y => g ((A.chart j).symm y)) (volume.restrict ((A.chart j) '' tsupport (P.χ j)))` using `hg.comp_aemeasurable (((A.chart j).continuousOn_symm.mono hCT).aemeasurable hC.measurableSet)`.

Establish `hχ1 : ∀ x, P.χ j x ≤ 1` using `fun x => by`. Rewrite using `[← P.sum_eq_one x]`. Conclude with `Finset.single_le_sum (fun k _ => P.nonneg k x) (Finset.mem_univ j)`. Establish `hCi : IntegrableOn (fun y => g ((A.chart j).symm y) * max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0) ((A.chart j) '' tsupport (P.χ j))`. Use `(hL.norm.const_mul |s|).mono' (hsymm.mul ((hcont.mono hCT).aemeasurable hC.measurableSet)).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations.

Establish `h0` using `P.nonneg j ((A.chart j).symm y)`. Establish `h1` using `hχ1 ((A.chart j).symm y)`. Rewrite using `[Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]`. Establish `hm : |max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0| ≤ |s| * |locDens A Φ j y|`. Rewrite using `[abs_of_nonneg (le_max_right _ _)]`.

Use `max_le ?_ (by positivity)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[abs_mul, abs_mul, abs_of_nonneg h0]`. Use `_ ≤ |s| * (1 * |locDens A Φ j y|) := by gcongr`. Use `_ = |s| * |locDens A Φ j y| := by ring`.

Combine the equalities or inequalities in the displayed calculation. Use `IntegrableOn.of_forall_diff_eq_zero hCi (A.chart j).open_target.measurableSet ?_` and prove the remaining obligations. Introduce `y hy`. Simplify using `[hz y hy.1 hy.2]`.
-/
private theorem integrableOn_part [CompactSpace X] [T2Space X] [BorelSpace X]
    (A : FinHolAtlas e X) (P : ChartPartition A) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (s : ℝ) (j : Fin A.n) (g : X → ℝ) (hg : Measurable g)
    (hgi : MIntegrable A Φ g) :
    IntegrableOn (fun y => g ((A.chart j).symm y) *
      max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0) (A.chart j).target := by
  obtain ⟨hC, hCT, hz⟩ := chart_weight_compact A P Φ j
  have hL := hgi j _ hCT hC
  have hw : ContinuousOn (fun y => s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))
      (A.chart j).target :=
    continuousOn_const.mul ((chiCont A P j).mul (locDensCont A Φ hΦ j))
  have hcont : ContinuousOn (fun y => max (s * (P.χ j ((A.chart j).symm y) *
      locDens A Φ j y)) 0) (A.chart j).target :=
    fun y hy => (hw y hy).max continuousWithinAt_const
  have hsymm : AEMeasurable (fun y => g ((A.chart j).symm y)) (volume.restrict
      ((A.chart j) '' tsupport (P.χ j))) :=
    hg.comp_aemeasurable (((A.chart j).continuousOn_symm.mono hCT).aemeasurable hC.measurableSet)
  have hχ1 : ∀ x, P.χ j x ≤ 1 := fun x => by
    rw [← P.sum_eq_one x]
    exact Finset.single_le_sum (fun k _ => P.nonneg k x) (Finset.mem_univ j)
  have hCi : IntegrableOn (fun y => g ((A.chart j).symm y) *
      max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0)
      ((A.chart j) '' tsupport (P.χ j)) := by
    refine (hL.norm.const_mul |s|).mono'
      (hsymm.mul ((hcont.mono hCT).aemeasurable hC.measurableSet)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    have h0 := P.nonneg j ((A.chart j).symm y)
    have h1 := hχ1 ((A.chart j).symm y)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
    have hm : |max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0| ≤
        |s| * |locDens A Φ j y| := by
      rw [abs_of_nonneg (le_max_right _ _)]
      refine max_le ?_ (by positivity)
      calc s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)
          ≤ |s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)| := le_abs_self _
        _ = |s| * (P.χ j ((A.chart j).symm y) * |locDens A Φ j y|) := by
          rw [abs_mul, abs_mul, abs_of_nonneg h0]
        _ ≤ |s| * (1 * |locDens A Φ j y|) := by gcongr
        _ = |s| * |locDens A Φ j y| := by ring
    calc |g ((A.chart j).symm y)| * |max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0|
        ≤ |g ((A.chart j).symm y)| * (|s| * |locDens A Φ j y|) := by gcongr
      _ = |s| * (|g ((A.chart j).symm y)| * |locDens A Φ j y|) := by ring
  refine IntegrableOn.of_forall_diff_eq_zero hCi (A.chart j).open_target.measurableSet ?_
  intro y hy
  simp [hz y hy.1 hy.2]

/- English proof (translation)
Establish `hT` using `(A.chart j).open_target.measurableSet`. Establish `hw : ContinuousOn (fun y => s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) (A.chart j).target` using `continuousOn_const.mul ((chiCont A P j).mul (locDensCont A Φ hΦ j))`. Establish `hf : AEMeasurable (fun y => (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)).toNNReal) (volume.restrict (A.chart j).target)` using `(hw.aemeasurable hT).real_toNNReal`. Establish `hsy : AEMeasurable (A.chart j).symm ((volume.restrict (A.chart j).target).withDensity fun y => ENNReal.ofReal (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)))` using `((A.chart j).continuousOn_symm.aemeasurable hT).mono_ac (withDensity_absolutelyContinuous _ _)`. Establish `hgm : AEStronglyMeasurable g (chartPartMeasure A P Φ s j)` using `hg.aestronglyMeasurable`.

Establish `hpart` using `integrableOn_part A P Φ hΦ s j g hg hgi`. Unfold `chartPartMeasure at hgm ⊢`. Prove the components needed by the constructor for the conclusion. Rewrite using `[integrable_map_measure hgm hsy]`. Use `(integrable_withDensity_iff_integrable_smul₀ hf).2 ?_` and prove the remaining obligations.

Use `hpart.congr (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[integral_map hsy hgm]`. Use `(integral_withDensity_eq_integral_smul₀ hf (fun y => g ((A.chart j).symm y))).trans ?_` and prove the remaining obligations.

Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_chartPartMeasure [CompactSpace X] [T2Space X] [BorelSpace X]
    (A : FinHolAtlas e X) (P : ChartPartition A) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (s : ℝ) (j : Fin A.n) (g : X → ℝ) (hg : Measurable g)
    (hgi : MIntegrable A Φ g) :
    Integrable g (chartPartMeasure A P Φ s j) ∧
      ∫ x, g x ∂chartPartMeasure A P Φ s j =
        ∫ y in (A.chart j).target, g ((A.chart j).symm y) *
          max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0 := by
  have hT := (A.chart j).open_target.measurableSet
  have hw : ContinuousOn (fun y => s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))
      (A.chart j).target :=
    continuousOn_const.mul ((chiCont A P j).mul (locDensCont A Φ hΦ j))
  have hf : AEMeasurable (fun y => (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)).toNNReal)
      (volume.restrict (A.chart j).target) := (hw.aemeasurable hT).real_toNNReal
  have hsy : AEMeasurable (A.chart j).symm ((volume.restrict (A.chart j).target).withDensity
      fun y => ENNReal.ofReal (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))) :=
    ((A.chart j).continuousOn_symm.aemeasurable hT).mono_ac (withDensity_absolutelyContinuous _ _)
  have hgm : AEStronglyMeasurable g (chartPartMeasure A P Φ s j) := hg.aestronglyMeasurable
  have hpart := integrableOn_part A P Φ hΦ s j g hg hgi
  unfold chartPartMeasure at hgm ⊢
  constructor
  · rw [integrable_map_measure hgm hsy]
    refine (integrable_withDensity_iff_integrable_smul₀ hf).2 ?_
    refine hpart.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Function.comp_apply, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal']
    ring
  · rw [integral_map hsy hgm]
    refine (integral_withDensity_eq_integral_smul₀ hf (fun y => g ((A.chart j).symm y))).trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal']
    ring

/- English proof (translation)
Use `Finset.sum_induction μ (fun ν => IsFiniteMeasure ν) (fun a b ha hb => ?_) ?_ (fun j _ => h j)` and prove the remaining obligations. Use `haveI := ha haveI := hb infer_instance`. Use `infer_instance`.
-/
private theorem isFiniteMeasure_sum' {α : Type} [MeasurableSpace α] {n : ℕ} (μ : Fin n → Measure α)
    (h : ∀ j, IsFiniteMeasure (μ j)) : IsFiniteMeasure (∑ j, μ j) := by
  refine Finset.sum_induction μ (fun ν => IsFiniteMeasure ν) (fun a b ha hb => ?_) ?_
    (fun j _ => h j)
  · haveI := ha
    haveI := hb
    infer_instance
  · infer_instance

/- English proof (translation)
Break down `le_total 0 a with h | h` into its components or cases. Rewrite using `[max_eq_left (by linarith : (0 : ℝ) ≤ 1 * a), max_eq_right (by linarith : -1 * a ≤ 0)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[max_eq_right (by linarith : 1 * a ≤ 0), max_eq_left (by linarith : (0 : ℝ) ≤ -1 * a)]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem mul_max_sub_mul_max_neg_eq_mul (a b : ℝ) : b * max (1 * a) 0 - b * max (-1 * a) 0 = b * a := by
  rcases le_total 0 a with h | h
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ 1 * a), max_eq_right (by linarith : -1 * a ≤ 0)]
    ring
  · rw [max_eq_right (by linarith : 1 * a ≤ 0), max_eq_left (by linarith : (0 : ℝ) ≤ -1 * a)]
    ring

/- English proof (translation)
Introduce `e X _ _ _ _ _ A Φ hΦ`. Establish `hP : Nonempty (ChartPartition A)` using `existsPartition A`. Use `⟨∑ j, chartPartMeasure A hP.some Φ 1 j, ∑ j, chartPartMeasure A hP.some Φ (-1) j, isFiniteMeasure_sum' _ (fun j => isFiniteMeasure_chartPartMeasure A hP.some Φ hΦ 1 j), isFiniteMeasure_sum' _ (fun j => isFiniteMeasure_chartPartMeasure A hP.some Φ hΦ (-1) j), ?_⟩` and prove the remaining obligations. Introduce `g hg hgi`. Establish `h1` using `fun j => integral_chartPartMeasure A hP.some Φ hΦ 1 j g hg hgi`.

Establish `h2` using `fun j => integral_chartPartMeasure A hP.some Φ hΦ (-1) j g hg hgi`. Use `⟨integrable_finset_sum_measure.2 (fun j _ => (h1 j).1), integrable_finset_sum_measure.2 (fun j _ => (h2 j).1), ?_⟩` and prove the remaining obligations. Rewrite using `[integral_finset_sum_measure (fun j _ => (h1 j).1), integral_finset_sum_measure (fun j _ => (h2 j).1), ← Finset.sum_sub_distrib]`. Unfold `mInt`. Rewrite using `[dif_pos hP]`.

Unfold `integralWith`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[(h1 j).2, (h2 j).2, ← integral_sub (integrableOn_part A hP.some Φ hΦ 1 j g hg hgi) (integrableOn_part A hP.some Φ hΦ (-1) j g hg hgi)]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[mul_max_sub_mul_max_neg_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mIntMeasure : MIntMeasureStatement := by
  intro e X _ _ _ _ _ A Φ hΦ
  have hP : Nonempty (ChartPartition A) := existsPartition A
  refine ⟨∑ j, chartPartMeasure A hP.some Φ 1 j, ∑ j, chartPartMeasure A hP.some Φ (-1) j,
    isFiniteMeasure_sum' _ (fun j => isFiniteMeasure_chartPartMeasure A hP.some Φ hΦ 1 j),
    isFiniteMeasure_sum' _ (fun j => isFiniteMeasure_chartPartMeasure A hP.some Φ hΦ (-1) j), ?_⟩
  intro g hg hgi
  have h1 := fun j => integral_chartPartMeasure A hP.some Φ hΦ 1 j g hg hgi
  have h2 := fun j => integral_chartPartMeasure A hP.some Φ hΦ (-1) j g hg hgi
  refine ⟨integrable_finset_sum_measure.2 (fun j _ => (h1 j).1),
    integrable_finset_sum_measure.2 (fun j _ => (h2 j).1), ?_⟩
  rw [integral_finset_sum_measure (fun j _ => (h1 j).1),
    integral_finset_sum_measure (fun j _ => (h2 j).1), ← Finset.sum_sub_distrib]
  unfold mInt
  rw [dif_pos hP]
  unfold integralWith
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [(h1 j).2, (h2 j).2, ← integral_sub (integrableOn_part A hP.some Φ hΦ 1 j g hg hgi)
    (integrableOn_part A hP.some Φ hΦ (-1) j g hg hgi)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  rw [mul_max_sub_mul_max_neg_eq_mul]
  ring

end

end ReciprocityTheory.AnForm.M

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarMassNearSmall
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartMassCompact
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFibreBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNullSmaller
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ENNReal NNReal

noncomputable section

namespace VarMassNearSmall

variable {n d : ℕ}

/- English proof (translation)
The claim follows from `|sheetSum J A F y| ≤ sheetSum J A G y := by classical unfold sheetSum rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin] refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_) split_ifs with h · exact hFG x _ · simp`.
-/
theorem abs_sheetSum_le (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    {F G : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ} (hFG : ∀ x s, |F x s| ≤ G x s)
    {y : Fin d → ℂ} (hfin : (fibre J A y).Finite) :
    |sheetSum J A F y| ≤ sheetSum J A G y := by
  classical
  unfold sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  split_ifs with h
  · exact hFG x _
  · simp

/- English proof (translation)
Set `E : ((Σ _ : Fin d, Fin 2) → ℝ) ≃L[ℝ] (Fin d → ℂ)` to `(Pi.basis (fun _ : Fin d => Complex.basisOneI)).equivFun.symm.toContinuousLinearEquiv`. Establish `hcard : Fintype.card (Σ _ : Fin d, Fin 2) = 2 * d`. Simplify using `[Fintype.card_sigma, mul_comm]`. Establish `hT : volume (E ⁻¹' S) = 0`. Rewrite using `[← hausdorffMeasure_pi_real, hcard]`.

Establish `h` using `E.symm.lipschitz.hausdorffMeasure_image_le (d := ((2 * d : ℕ) : ℝ)) (by positivity) S`. Rewrite `h` using `[hS, mul_zero, nonpos_iff_eq_zero, ContinuousLinearEquiv.image_symm_eq_preimage]`. Conclude with `h`. Establish `: (Measure.map E volume).IsAddHaarMeasure` using `E.isAddHaarMeasure_map volume`. Establish `hac : (volume : Measure (Fin d → ℂ)) ≪ Measure.map E volume` using `Measure.absolutelyContinuous_isAddHaarMeasure _ _`.

Apply `hac` to reduce the goal to its premises. Conclude with `(E.toHomeomorph.toMeasurableEquiv.map_apply S).trans hT`.
-/
theorem volume_eq_zero_of_hausdorff {S : Set (Fin d → ℂ)} (hS : μH[((2 * d : ℕ) : ℝ)] S = 0) :
    volume S = 0 := by
  let E : ((Σ _ : Fin d, Fin 2) → ℝ) ≃L[ℝ] (Fin d → ℂ) :=
    (Pi.basis (fun _ : Fin d => Complex.basisOneI)).equivFun.symm.toContinuousLinearEquiv
  have hcard : Fintype.card (Σ _ : Fin d, Fin 2) = 2 * d := by
    simp [Fintype.card_sigma, mul_comm]
  have hT : volume (E ⁻¹' S) = 0 := by
    rw [← hausdorffMeasure_pi_real, hcard]
    have h := E.symm.lipschitz.hausdorffMeasure_image_le (d := ((2 * d : ℕ) : ℝ)) (by positivity) S
    rw [hS, mul_zero, nonpos_iff_eq_zero, ContinuousLinearEquiv.image_symm_eq_preimage] at h
    exact h
  have : (Measure.map E volume).IsAddHaarMeasure := E.isAddHaarMeasure_map volume
  have hac : (volume : Measure (Fin d → ℂ)) ≪ Measure.map E volume :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  apply hac
  exact (E.toHomeomorph.toMeasurableEquiv.map_apply S).trans hT

/- English proof (translation)
Establish `hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (W ⊔ I)) < d` using `(ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective le_sup_right)).trans_lt hI`. Establish `h0` using `NullSmaller.proof n d (W ⊔ I) hdim`. Set `L : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin d → ℂ)` to `(Matrix.mulVecLin A).toContinuousLinearMap.comp (EuclideanSpace.equiv (Fin n) ℂ).toContinuousLinearMap`. Establish `hsub : A.mulVec '' (zeroSet W ∩ zeroSet I) ⊆ L '' zeroSetEuc (W ⊔ I)`. Introduce and unpack `_ ⟨x, ⟨hxW, hxI⟩, rfl⟩`.

Use `⟨(EuclideanSpace.equiv (Fin n) ℂ).symm x, fun q hq => ?_, by simp only [L, ContinuousLinearMap.comp_apply]; rfl⟩` and prove the remaining obligations. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hq`. Establish `hx : (fun i => ((EuclideanSpace.equiv (Fin n) ℂ).symm x) i) = x` using `rfl`. Rewrite using `[hx, map_add, hxW a ha, hxI b hb, add_zero]`. Use `volume_eq_zero_of_hausdorff (le_antisymm ?_ bot_le)` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem volume_image_eq_zero (W I : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hI : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < d) :
    volume (A.mulVec '' (zeroSet W ∩ zeroSet I)) = 0 := by
  have hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (W ⊔ I)) < d :=
    (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective le_sup_right)).trans_lt hI
  have h0 := NullSmaller.proof n d (W ⊔ I) hdim
  let L : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin d → ℂ) :=
    (Matrix.mulVecLin A).toContinuousLinearMap.comp (EuclideanSpace.equiv (Fin n) ℂ).toContinuousLinearMap
  have hsub : A.mulVec '' (zeroSet W ∩ zeroSet I) ⊆ L '' zeroSetEuc (W ⊔ I) := by
    rintro _ ⟨x, ⟨hxW, hxI⟩, rfl⟩
    refine ⟨(EuclideanSpace.equiv (Fin n) ℂ).symm x, fun q hq => ?_, by simp only [L, ContinuousLinearMap.comp_apply]; rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hq
    have hx : (fun i => ((EuclideanSpace.equiv (Fin n) ℂ).symm x) i) = x := rfl
    rw [hx, map_add, hxW a ha, hxI b hb, add_zero]
  refine volume_eq_zero_of_hausdorff (le_antisymm ?_ bot_le)
  calc μH[((2 * d : ℕ) : ℝ)] (A.mulVec '' (zeroSet W ∩ zeroSet I))
      ≤ μH[((2 * d : ℕ) : ℝ)] (L '' zeroSetEuc (W ⊔ I)) := measure_mono hsub
    _ ≤ _ := L.lipschitz.hausdorffMeasure_image_le (by positivity) _
    _ = 0 := by rw [h0, mul_zero]

end VarMassNearSmall

open VarMassNearSmall in

/- English proof (translation)
Introduce `n d W I φ f hW hdim hφ hI hf hfc δ hδ`. Distinguish the cases in `hA : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection W A`. Use `swap`. Use `⟨Set.univ, isOpen_univ, Set.subset_univ _, fun χ _ _ _ => ?_⟩` and prove the remaining obligations. Unfold `varInt`.

Rewrite using `[dif_neg hA, abs_zero]`. Conclude with `hδ.le`. Use `set A := hA.choose with hAdef`. Establish `hAf : IsFiniteProjection W A` using `hA.choose_spec`. Establish `hvar : ∀ g, varInt W d g φ = ∫ y, chartDens W A g φ y` using `fun g => by`.

Unfold `varInt chartInt`. Rewrite using `[dif_pos hA]`. Establish `hfin : ∀ y, (fibre W A y).Finite` using `fun y => (FibreBound.proof n d W A hW hdim hAf y).2.1`. Establish `hS : IsClosed (zeroSet I)` using `SheetSumMeasurable.isClosed_zeroSet I`. Use `set U : ℕ → Set (Fin n → ℂ) := fun k => Metric.thickening (1 / ((k : ℝ) + 1)) (zeroSet I) with hU`.

Use `set F : ℕ → (Fin d → ℂ) → ℝ := fun k => chartAbsDens W A ((U k).indicator fun x => |f x|) φ with hF`. Use `set G := chartAbsDens W A (fun x => |f x|) φ with hG`. Establish `hGi : Integrable G` using `hCMC n d W A _ φ hW hdim hAf (continuous_abs.comp hf).continuousOn hφ (Or.inl (hfc.comp_left abs_zero))`. Establish `hFm : ∀ k, Measurable (F k)` using `fun k => (SheetSumMeasurable.proof n d W A _ φ hW hdim hAf ((continuous_abs.comp hf).measurable.indicator Metric.isOpen_thickening.measurableSet) hφ).2`. Establish `hFG : ∀ k y, ‖F k y‖ ≤ G y`.

Introduce `k y`. Rewrite using `[Real.norm_eq_abs]`. Use `abs_sheetSum_le W A (fun x s => ?_) (hfin y)` and prove the remaining obligations. Rewrite using `[abs_abs, abs_mul, abs_mul]`. Use `mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)` and prove the remaining obligations.

Distinguish the cases in `hx : x ∈ U k`. Simplify using `[Set.indicator_of_mem hx]`. Rewrite using `[Set.indicator_of_notMem hx, abs_zero]`. Conclude with `abs_nonneg _`. Establish `hlim : ∀ᵐ y, Tendsto (fun k => F k y) atTop (𝓝 0)` using `by filter_upwards [measure_eq_zero_iff_ae_notMem.1 (volume_image_eq_zero W I A hI)] with y hy`.

Establish `hx : ∀ x ∈ fibre W A y, ∀ᶠ k in atTop, x ∉ U k`. Introduce `x hxf`. Establish `hxS : x ∉ zeroSet I` using `fun h => hy ⟨x, ⟨hxf.1, h⟩, hxf.2⟩`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.1 hS.isOpen_compl x hxS`. Take `⟨K, hK⟩` from `exists_nat_one_div_lt hε`.

Use `filter_upwards [eventually_ge_atTop K] with k hk hxU`. Take `⟨z, hz, hdist⟩` from `Metric.mem_thickening_iff.1 hxU`. Establish `hKk : (K : ℝ) + 1 ≤ (k : ℝ) + 1`. Establish `: (K : ℝ) ≤ k` using `by exact_mod_cast hk`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hle : 1 / ((k : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1)` using `one_div_le_one_div_of_le (by positivity) hKk`. Conclude with `hball (show dist z x < ε by rw [dist_comm]; linarith) hz`. Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations. Use `filter_upwards [(eventually_all_finite (hfin y)).2 hx] with k hk`. Use `symm`.

Use `show sheetSum W A _ y = 0`. Unfold `sheetSum`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ (hfin y)]`. Use `Finset.sum_eq_zero fun x hxm => ?_` and prove the remaining obligations. Rewrite `hxm` using `[Set.Finite.mem_toFinset]`.

Apply the tactic sequence `split_ifs <;> simp [Set.indicator_of_notMem (hk x hxm)]`. Establish `hT` using `tendsto_integral_of_dominated_convergence G (fun k => (hFm k).aestronglyMeasurable) hGi (fun k => Eventually.of_forall (hFG k)) hlim`. Simplify using `only [integral_zero] at hT`. Take `⟨k, hk⟩` from `((tendsto_order.1 hT).2 δ hδ).exists`. Use `⟨U k, Metric.isOpen_thickening, Metric.self_subset_thickening (by positivity) _, fun χ hχ hχ1 hχU => ?_⟩` and prove the remaining obligations.

Establish `hFi : Integrable (F k)` using `hGi.mono' (hFm k).aestronglyMeasurable (Eventually.of_forall (hFG k))`. Establish `hpt : ∀ y, ‖chartDens W A (fun x => χ x * f x) φ y‖ ≤ F k y`. Introduce `y`. Rewrite using `[Real.norm_eq_abs]`. Use `abs_sheetSum_le W A (fun x s => ?_) (hfin y)` and prove the remaining obligations.

Distinguish the cases in `hx : x ∈ U k`. Rewrite using `[Set.indicator_of_mem hx, abs_mul, abs_mul, abs_mul, abs_abs]`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) (hχ1 x)) (abs_nonneg _)`. Establish `h0 : χ x = 0` using `image_eq_zero_of_notMem_tsupport fun h => hx (hχU h)`. Simplify using `only [h0, zero_mul, abs_zero]`.

Check the signs of the components of the expression. Establish `h1` using `norm_integral_le_of_norm_le hFi (Eventually.of_forall hpt)`. Rewrite `h1` using `[Real.norm_eq_abs, ← hvar]`. Conclude with `h1.trans hk.le`.
-/
theorem VarMassNearSmall.proof (hCMC : ChartMassCompact.Statement) : VarMassNearSmall.Statement := by
  classical
  intro n d W I φ f hW hdim hφ hI hf hfc δ hδ
  by_cases hA : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection W A
  swap
  · refine ⟨Set.univ, isOpen_univ, Set.subset_univ _, fun χ _ _ _ => ?_⟩
    unfold varInt
    rw [dif_neg hA, abs_zero]
    exact hδ.le
  set A := hA.choose with hAdef
  have hAf : IsFiniteProjection W A := hA.choose_spec
  have hvar : ∀ g, varInt W d g φ = ∫ y, chartDens W A g φ y := fun g => by
    unfold varInt chartInt
    rw [dif_pos hA]
  have hfin : ∀ y, (fibre W A y).Finite := fun y => (FibreBound.proof n d W A hW hdim hAf y).2.1
  have hS : IsClosed (zeroSet I) := SheetSumMeasurable.isClosed_zeroSet I
  set U : ℕ → Set (Fin n → ℂ) := fun k => Metric.thickening (1 / ((k : ℝ) + 1)) (zeroSet I) with hU
  set F : ℕ → (Fin d → ℂ) → ℝ := fun k => chartAbsDens W A ((U k).indicator fun x => |f x|) φ with hF
  set G := chartAbsDens W A (fun x => |f x|) φ with hG
  have hGi : Integrable G := hCMC n d W A _ φ hW hdim hAf (continuous_abs.comp hf).continuousOn hφ
    (Or.inl (hfc.comp_left abs_zero))
  have hFm : ∀ k, Measurable (F k) := fun k => (SheetSumMeasurable.proof n d W A _ φ hW hdim hAf
    ((continuous_abs.comp hf).measurable.indicator Metric.isOpen_thickening.measurableSet) hφ).2
  have hFG : ∀ k y, ‖F k y‖ ≤ G y := by
    intro k y
    rw [Real.norm_eq_abs]
    refine abs_sheetSum_le W A (fun x s => ?_) (hfin y)
    rw [abs_abs, abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    by_cases hx : x ∈ U k
    · simp [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, abs_zero]
      exact abs_nonneg _
  have hlim : ∀ᵐ y, Tendsto (fun k => F k y) atTop (𝓝 0) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (volume_image_eq_zero W I A hI)] with y hy
    have hx : ∀ x ∈ fibre W A y, ∀ᶠ k in atTop, x ∉ U k := by
      intro x hxf
      have hxS : x ∉ zeroSet I := fun h => hy ⟨x, ⟨hxf.1, h⟩, hxf.2⟩
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hS.isOpen_compl x hxS
      obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
      filter_upwards [eventually_ge_atTop K] with k hk hxU
      obtain ⟨z, hz, hdist⟩ := Metric.mem_thickening_iff.1 hxU
      have hKk : (K : ℝ) + 1 ≤ (k : ℝ) + 1 := by
        have : (K : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      have hle : 1 / ((k : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) hKk
      exact hball (show dist z x < ε by rw [dist_comm]; linarith) hz
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(eventually_all_finite (hfin y)).2 hx] with k hk
    symm
    show sheetSum W A _ y = 0
    unfold sheetSum
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
    refine Finset.sum_eq_zero fun x hxm => ?_
    rw [Set.Finite.mem_toFinset] at hxm
    split_ifs <;> simp [Set.indicator_of_notMem (hk x hxm)]
  have hT := tendsto_integral_of_dominated_convergence G (fun k => (hFm k).aestronglyMeasurable) hGi
    (fun k => Eventually.of_forall (hFG k)) hlim
  simp only [integral_zero] at hT
  obtain ⟨k, hk⟩ := ((tendsto_order.1 hT).2 δ hδ).exists
  refine ⟨U k, Metric.isOpen_thickening, Metric.self_subset_thickening (by positivity) _,
    fun χ hχ hχ1 hχU => ?_⟩
  have hFi : Integrable (F k) := hGi.mono' (hFm k).aestronglyMeasurable (Eventually.of_forall (hFG k))
  have hpt : ∀ y, ‖chartDens W A (fun x => χ x * f x) φ y‖ ≤ F k y := by
    intro y
    rw [Real.norm_eq_abs]
    refine abs_sheetSum_le W A (fun x s => ?_) (hfin y)
    by_cases hx : x ∈ U k
    · rw [Set.indicator_of_mem hx, abs_mul, abs_mul, abs_mul, abs_abs]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) (hχ1 x)) (abs_nonneg _)
    · have h0 : χ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hχU h)
      simp only [h0, zero_mul, abs_zero]
      positivity
  have h1 := norm_integral_le_of_norm_le hFi (Eventually.of_forall hpt)
  rw [Real.norm_eq_abs, ← hvar] at h1
  exact h1.trans hk.le

end

end GroundTheory.Heights₂.Heights

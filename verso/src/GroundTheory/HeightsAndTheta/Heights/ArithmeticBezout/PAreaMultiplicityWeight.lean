import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsAreaMultiplicityWeight
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAreaMultiplicity
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module Set Filter Function

open scoped ENNReal NNReal

noncomputable section

/- English proof (translation)
Break down `hs.exists_measurable_subset_ae_eq with ⟨t, ts, ht, t_eq_s⟩` into its components or cases. Establish `himg : f '' t =ᵐ[μ] f '' s`. Establish `hst : s = t ∪ (s \ t)` using `by simp [union_eq_self_of_subset_left ts]`. Rewrite using `[hst, image_union]`. Use `(union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr ?_)).symm` and prove the remaining obligations.

Use `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero _ (fun x hx ↦ ?_) (ae_eq_set.1 t_eq_s).2` and prove the remaining obligations. Conclude with `(hf' x hx.1).differentiableWithinAt.mono sdiff_subset`. Rewrite using `[setLIntegral_congr t_eq_s.symm, ← setLIntegral_congr himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul μ ht (fun x hx => (hf' x (ts hx)).mono ts) (hf.mono ts)]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Conclude with `mul_comm _ _`.
-/
theorem AreaMultiplicityWeight.setLIntegral_comp_mul_abs_det₀ {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
    (hs : NullMeasurableSet s μ) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf : InjOn f s) (g : E → ℝ≥0∞) :
    ∫⁻ x in s, g (f x) * ENNReal.ofReal |(f' x).det| ∂μ = ∫⁻ y in f '' s, g y ∂μ := by
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, ts, ht, t_eq_s⟩
  have himg : f '' t =ᵐ[μ] f '' s := by
    have hst : s = t ∪ (s \ t) := by simp [union_eq_self_of_subset_left ts]
    rw [hst, image_union]
    refine (union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr ?_)).symm
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero _ (fun x hx ↦ ?_)
      (ae_eq_set.1 t_eq_s).2
    exact (hf' x hx.1).differentiableWithinAt.mono sdiff_subset
  rw [setLIntegral_congr t_eq_s.symm, ← setLIntegral_congr himg,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul μ ht (fun x hx => (hf' x (ts hx)).mono ts)
      (hf.mono ts)]
  congr 1
  funext x
  exact mul_comm _ _

/- English proof (translation)
Introduce `E _ _ _ _ _ μ _ A f f' hA hf'`. Use `set B : Set E := {x ∈ A | (f' x).det ≠ 0} with hBdef`. Establish `hBA : B ⊆ A` using `sep_subset _ _`. Establish `hB : NullMeasurableSet B μ`. Take `⟨d, hdm, hfd⟩ : AEMeasurable (fun x => (f' x).det) (μ.restrict A)` from `ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable (aemeasurable_fderivWithin μ hA hf')`.

Use `(hA.inter (hdm (measurableSet_singleton 0).compl)).nullMeasurableSet.congr ?_` and prove the remaining obligations. Use `filter_upwards [(ae_restrict_iff' hA).1 hfd] with x hx`. Express the relevant statement in the definitionally equal form `(x ∈ A ∩ d ⁻¹' {0}ᶜ) = (x ∈ B)`. Rewrite using `[eq_iff_iff]`. Distinguish the cases in `hxA : x ∈ A`.

Simplify using `[B, hxA, hx hxA]`. Simplify using `[B, hxA]`. Establish `hZ : μ (f '' {x ∈ A | (f' x).det = 0}) = 0` using `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ (fun x hx => (hf' x hx.1).mono (sep_subset _ _)) (fun x hx => hx.2)`. Set `r : (E →L[ℝ] E) → ℝ≥0` to `fun L => (‖L.inverse‖₊ + 1)⁻¹`. Take `⟨t, L, htd, htm, hcov, happ, hL⟩` from `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f B f' (fun x hx => (hf' x hx.1).mono hBA) r (fun _ => inv_ne_zero (by positivity))`.

Use `set P : ℕ → Set E := fun n => B ∩ t n with hPdef`. Establish `hPm : ∀ n, NullMeasurableSet (P n) μ` using `fun n => hB.inter (htm n).nullMeasurableSet`. Establish `hPd : Pairwise (Disjoint on P)` using `fun m n hmn => (htd hmn).mono inter_subset_right inter_subset_right`. Establish `hPA : ∀ n, P n ⊆ A` using `fun n => inter_subset_left.trans hBA`. Establish `hderP : ∀ n, ∀ x ∈ P n, HasFDerivWithinAt f (f' x) (P n) x` using `fun n x hx => (hf' x (hPA n hx)).mono (hPA n)`.

Establish `hinj : ∀ n, InjOn f (P n)`. Introduce `n`. Break down `(P n).eq_empty_or_nonempty with h | ⟨x, hx⟩` into its components or cases. Rewrite using `[h]`. Conclude with `injOn_empty f`.

Take `⟨y, hy, hLy⟩` from `hL ⟨x, hx.1⟩ n`. Use `set e := (f' y).toContinuousLinearEquivOfDetNeZero hy.2`. Establish `he : (e : E →L[ℝ] E) = L n`. Rewrite using `[hLy]`. Conclude with `ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _`.

Establish `ha` using `happ n`. Rewrite `ha` using `[← he]`. Use `ha.injOn ?_` and prove the remaining obligations. Break down `subsingleton_or_nontrivial E with hE | hE` into its components or cases. Conclude with `Or.inl hE`.

Use `right`. Establish `hr : r (e : E →L[ℝ] E) = (‖(e.symm : E →L[ℝ] E)‖₊ + 1)⁻¹`. Simplify using `only [r, ContinuousLinearMap.inverse_equiv]`. Rewrite using `[hr]`. Establish `hpos : 0 < ‖(e.symm : E →L[ℝ] E)‖₊`.

Rewrite using `[pos_iff_ne_zero, ne_eq, nnnorm_eq_zero]`. Introduce `h0`. Take `⟨z, hz⟩` from `exists_ne (0 : E)`. Apply `hz` to reduce the goal to its premises. Simplify using `using congrArg (fun T : E →L[ℝ] E => T (e z)) h0`.

Conclude with `(inv_lt_inv₀ (by positivity) hpos).2 (lt_add_one _)`. Establish `hBU : B = ⋃ n, P n`. Rewrite using `[← inter_iUnion]`. Conclude with `(inter_eq_left.2 hcov).symm`. Establish `himg : ∀ n, NullMeasurableSet (f '' P n) μ` using `fun n => nullMeasurable_image_of_fderivWithin μ (hPm n) (hderP n) (hinj n)`.

Establish `hNae : ∀ᵐ y ∂μ, ∑' n, (f '' P n).indicator (1 : E → ℝ≥0∞) y = (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞)` using `by filter_upwards [measure_eq_zero_iff_ae_notMem.1 hZ] with y hy`. Establish `hU : {x ∈ A | f x = y} = ⋃ n, {x ∈ P n | f x = y}`. Use extensionality with `x`. Simplify using `only [mem_ofPred_eq, mem_iUnion]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hxA, hxy⟩`. Establish `hxB : x ∈ B` using `⟨hxA, fun hd => hy ⟨x, ⟨hxA, hd⟩, hxy⟩⟩`. Take `⟨n, hn⟩` from `mem_iUnion.1 (hcov hxB)`. Conclude with `⟨n, ⟨hxB, hn⟩, hxy⟩`. Introduce and unpack `⟨n, hxP, hxy⟩`.

Conclude with `⟨hPA n hxP, hxy⟩`. Rewrite using `[hU, encard_iUnion_nat_eq_tsum _ (fun m n hmn => (hPd hmn).mono (sep_subset _ _) (sep_subset _ _))]`. Use `tsum_congr fun n => ?_` and prove the remaining obligations. Distinguish the cases in `hyn : y ∈ f '' P n`. Take `⟨x, hx, rfl⟩` from `hyn`.

Establish `hs : {z ∈ P n | f z = f x} = {x}`. Use extensionality with `z`. Simplify using `only [mem_ofPred_eq, mem_singleton_iff]`. Conclude with `⟨fun h => hinj n h.1 hx h.2, fun h => by subst h; exact ⟨hx, rfl⟩⟩`. Rewrite using `[hs, encard_singleton, indicator_of_mem (mem_image_of_mem f hx)]`.

Simplify using the standard rewrite rules. Establish `hs : {z ∈ P n | f z = y} = ∅`. Use extensionality with `z`. Simplify using `only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]`. Conclude with `fun hz e => hyn ⟨z, hz, e⟩`.

Rewrite using `[hs, encard_empty]`. Simplify using `[hyn]`. Use `⟨(AEMeasurable.tsum fun n => aemeasurable_one.indicator₀ (himg n)).congr hNae, fun g hg => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← lintegral_indicator hA, ← lintegral_indicator₀ hB]`.

Use `congr 1`. Use extensionality with `x`. Distinguish the cases in `hx : x ∈ A`. Distinguish the cases in `hd : (f' x).det = 0`. Simplify using `[indicator, hx, hd, B]`.

Simplify using `[indicator, hx, hd, B]`. Establish `: x ∉ B` using `fun h => hx h.1`. Simplify using `[hx, this]`. Use `_ = ∑' n, ∫⁻ x in P n, g (f x) * ENNReal.ofReal |(f' x).det| ∂μ := by`. Rewrite using `[hBU]`.

Conclude with `lintegral_iUnion₀ hPm (fun m n hmn => (hPd hmn).aedisjoint) _`. Use `_ = ∑' n, ∫⁻ y in f '' P n, g y ∂μ := tsum_congr fun n => AreaMultiplicityWeight.setLIntegral_comp_mul_abs_det₀ μ (hPm n) (hderP n) (hinj n) g`. Use `_ = ∑' n, ∫⁻ y, (f '' P n).indicator g y ∂μ := tsum_congr fun n => (lintegral_indicator₀ (himg n) g).symm`. Use `_ = ∫⁻ y, ∑' n, (f '' P n).indicator g y ∂μ := (lintegral_tsum fun n => hg.aemeasurable.indicator₀ (himg n)).symm`. Use `_ = ∫⁻ y, (∑' n, (f '' P n).indicator (1 : E → ℝ≥0∞) y) * g y ∂μ := by`.

Use `congr 1`. Use function extensionality and compare the values at `y`. Rewrite using `[← ENNReal.tsum_mul_right]`. Use `tsum_congr fun n => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases h : y ∈ f '' P n <;> simp [h]`.

Use `_ = ∫⁻ y, (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) * g y ∂μ := by`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hNae] with y hy`. Rewrite using `[hy]`.
-/
theorem AreaMultiplicityWeight.proof : AreaMultiplicityWeight.Statement := by
  intro E _ _ _ _ _ μ _ A f f' hA hf'
  classical
  set B : Set E := {x ∈ A | (f' x).det ≠ 0} with hBdef
  have hBA : B ⊆ A := sep_subset _ _

  have hB : NullMeasurableSet B μ := by
    obtain ⟨d, hdm, hfd⟩ : AEMeasurable (fun x => (f' x).det) (μ.restrict A) :=
      ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable
        (aemeasurable_fderivWithin μ hA hf')
    refine (hA.inter (hdm (measurableSet_singleton 0).compl)).nullMeasurableSet.congr ?_
    filter_upwards [(ae_restrict_iff' hA).1 hfd] with x hx
    change (x ∈ A ∩ d ⁻¹' {0}ᶜ) = (x ∈ B)
    rw [eq_iff_iff]
    by_cases hxA : x ∈ A
    · simp [B, hxA, hx hxA]
    · simp [B, hxA]

  have hZ : μ (f '' {x ∈ A | (f' x).det = 0}) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (fun x hx => (hf' x hx.1).mono (sep_subset _ _)) (fun x hx => hx.2)

  let r : (E →L[ℝ] E) → ℝ≥0 := fun L => (‖L.inverse‖₊ + 1)⁻¹
  obtain ⟨t, L, htd, htm, hcov, happ, hL⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f B f'
      (fun x hx => (hf' x hx.1).mono hBA) r (fun _ => inv_ne_zero (by positivity))
  set P : ℕ → Set E := fun n => B ∩ t n with hPdef
  have hPm : ∀ n, NullMeasurableSet (P n) μ := fun n => hB.inter (htm n).nullMeasurableSet
  have hPd : Pairwise (Disjoint on P) := fun m n hmn =>
    (htd hmn).mono inter_subset_right inter_subset_right
  have hPA : ∀ n, P n ⊆ A := fun n => inter_subset_left.trans hBA
  have hderP : ∀ n, ∀ x ∈ P n, HasFDerivWithinAt f (f' x) (P n) x := fun n x hx =>
    (hf' x (hPA n hx)).mono (hPA n)
  have hinj : ∀ n, InjOn f (P n) := by
    intro n
    rcases (P n).eq_empty_or_nonempty with h | ⟨x, hx⟩
    · rw [h]; exact injOn_empty f
    obtain ⟨y, hy, hLy⟩ := hL ⟨x, hx.1⟩ n
    set e := (f' y).toContinuousLinearEquivOfDetNeZero hy.2
    have he : (e : E →L[ℝ] E) = L n := by
      rw [hLy]; exact ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
    have ha := happ n
    rw [← he] at ha
    refine ha.injOn ?_
    rcases subsingleton_or_nontrivial E with hE | hE
    · exact Or.inl hE
    right
    have hr : r (e : E →L[ℝ] E) = (‖(e.symm : E →L[ℝ] E)‖₊ + 1)⁻¹ := by
      simp only [r, ContinuousLinearMap.inverse_equiv]
    rw [hr]
    have hpos : 0 < ‖(e.symm : E →L[ℝ] E)‖₊ := by
      rw [pos_iff_ne_zero, ne_eq, nnnorm_eq_zero]
      intro h0
      obtain ⟨z, hz⟩ := exists_ne (0 : E)
      apply hz
      simpa using congrArg (fun T : E →L[ℝ] E => T (e z)) h0
    exact (inv_lt_inv₀ (by positivity) hpos).2 (lt_add_one _)
  have hBU : B = ⋃ n, P n := by
    rw [← inter_iUnion]; exact (inter_eq_left.2 hcov).symm
  have himg : ∀ n, NullMeasurableSet (f '' P n) μ := fun n =>
    nullMeasurable_image_of_fderivWithin μ (hPm n) (hderP n) (hinj n)

  have hNae : ∀ᵐ y ∂μ, ∑' n, (f '' P n).indicator (1 : E → ℝ≥0∞) y =
      (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hZ] with y hy
    have hU : {x ∈ A | f x = y} = ⋃ n, {x ∈ P n | f x = y} := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion]
      constructor
      · rintro ⟨hxA, hxy⟩
        have hxB : x ∈ B := ⟨hxA, fun hd => hy ⟨x, ⟨hxA, hd⟩, hxy⟩⟩
        obtain ⟨n, hn⟩ := mem_iUnion.1 (hcov hxB)
        exact ⟨n, ⟨hxB, hn⟩, hxy⟩
      · rintro ⟨n, hxP, hxy⟩
        exact ⟨hPA n hxP, hxy⟩
    rw [hU, encard_iUnion_nat_eq_tsum _ (fun m n hmn => (hPd hmn).mono (sep_subset _ _)
      (sep_subset _ _))]
    refine tsum_congr fun n => ?_
    by_cases hyn : y ∈ f '' P n
    · obtain ⟨x, hx, rfl⟩ := hyn
      have hs : {z ∈ P n | f z = f x} = {x} := by
        ext z
        simp only [mem_ofPred_eq, mem_singleton_iff]
        exact ⟨fun h => hinj n h.1 hx h.2, fun h => by subst h; exact ⟨hx, rfl⟩⟩
      rw [hs, encard_singleton, indicator_of_mem (mem_image_of_mem f hx)]
      simp
    · have hs : {z ∈ P n | f z = y} = ∅ := by
        ext z
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun hz e => hyn ⟨z, hz, e⟩
      rw [hs, encard_empty]
      simp [hyn]
  refine ⟨(AEMeasurable.tsum fun n => aemeasurable_one.indicator₀ (himg n)).congr hNae,
    fun g hg => ?_⟩
  calc ∫⁻ x in A, g (f x) * ENNReal.ofReal |(f' x).det| ∂μ
      = ∫⁻ x in B, g (f x) * ENNReal.ofReal |(f' x).det| ∂μ := by
        rw [← lintegral_indicator hA, ← lintegral_indicator₀ hB]
        congr 1; ext x
        by_cases hx : x ∈ A
        · by_cases hd : (f' x).det = 0
          · simp [indicator, hx, hd, B]
          · simp [indicator, hx, hd, B]
        · have : x ∉ B := fun h => hx h.1
          simp [hx, this]
    _ = ∑' n, ∫⁻ x in P n, g (f x) * ENNReal.ofReal |(f' x).det| ∂μ := by
        rw [hBU]; exact lintegral_iUnion₀ hPm (fun m n hmn => (hPd hmn).aedisjoint) _
    _ = ∑' n, ∫⁻ y in f '' P n, g y ∂μ := tsum_congr fun n =>
        AreaMultiplicityWeight.setLIntegral_comp_mul_abs_det₀ μ (hPm n) (hderP n) (hinj n) g
    _ = ∑' n, ∫⁻ y, (f '' P n).indicator g y ∂μ :=
        tsum_congr fun n => (lintegral_indicator₀ (himg n) g).symm
    _ = ∫⁻ y, ∑' n, (f '' P n).indicator g y ∂μ :=
        (lintegral_tsum fun n => hg.aemeasurable.indicator₀ (himg n)).symm
    _ = ∫⁻ y, (∑' n, (f '' P n).indicator (1 : E → ℝ≥0∞) y) * g y ∂μ := by
        congr 1; funext y
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr fun n => ?_
        by_cases h : y ∈ f '' P n <;> simp [h]
    _ = ∫⁻ y, (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) * g y ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hNae] with y hy
        rw [hy]

end

end GroundTheory.Heights₂.Heights

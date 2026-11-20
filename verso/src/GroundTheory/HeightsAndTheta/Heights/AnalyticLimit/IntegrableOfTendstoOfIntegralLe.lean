import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureB
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open ReciprocityTheory.AnForm (hessC)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh locDens mInt MIntegrable)

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X]

/- English proof (translation)
Establish `h : fderiv ℝ (fun y => f y + c) = fderiv ℝ f` using `funext fun _ => fderiv_add_const c`. Unfold `hessC`. Rewrite using `[h]`.
-/
theorem hessC_add_const_fun (f : (Fin D → ℂ) → ℝ) (c : ℝ) (z : Fin D → ℂ) :
    hessC (fun y => f y + c) z = hessC f z := by
  have h : fderiv ℝ (fun y => f y + c) = fderiv ℝ f := funext fun _ => fderiv_add_const c
  unfold hessC
  rw [h]

/- English proof (translation)
Unfold `ReciprocityTheory.AnForm.M.locDens`. Use `ReciprocityTheory.AnForm.M.maDens_congr_hessC _ _ _ fun i => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `hc i`. Establish `hev : (fun y' => (potForm th (v i)).φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[𝓝 y] fun y' => (potForm th (u i)).φ ((A.chart j).symm y) ((A.chart j).symm y') + c` using `by filter_upwards [((A.chart j).isOpen_inter_preimage_symm hW).mem_nhds ⟨hy, hyW⟩] with y' hy' show th.φ _ _ + v i _ = th.φ _ _ + u i _ + c`. Rewrite using `[hc _ hy'.2]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `(ReciprocityTheory.AnForm.M.hessCGerm _ _ _ hev).trans (hessC_add_const_fun _ c y)`.
-/
theorem locDens_potForm_congr (A : FinHolAtlas D X) (th : LocPot X) (u v : Fin D → X → ℝ)
    (W : Set X) (hW : IsOpen W) (j : Fin A.n) {y : Fin D → ℂ} (hy : y ∈ (A.chart j).target)
    (hyW : (A.chart j).symm y ∈ W) (hc : ∀ i, ∃ c : ℝ, ∀ x ∈ W, v i x = u i x + c) :
    locDens A (fun i => potForm th (v i)) j y = locDens A (fun i => potForm th (u i)) j y := by
  unfold ReciprocityTheory.AnForm.M.locDens
  refine ReciprocityTheory.AnForm.M.maDens_congr_hessC _ _ _ fun i => ?_
  obtain ⟨c, hc⟩ := hc i
  have hev : (fun y' => (potForm th (v i)).φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[𝓝 y]
      fun y' => (potForm th (u i)).φ ((A.chart j).symm y) ((A.chart j).symm y') + c := by
    filter_upwards [((A.chart j).isOpen_inter_preimage_symm hW).mem_nhds ⟨hy, hyW⟩] with y' hy'
    show th.φ _ _ + v i _ = th.φ _ _ + u i _ + c
    rw [hc _ hy'.2]
    ring
  exact (ReciprocityTheory.AnForm.M.hessCGerm _ _ _ hev).trans (hessC_add_const_fun _ c y)

/- English proof (translation)
The claim follows from `((A.chart j).isOpen_inter_preimage_symm hS).measurableSet`.
-/
theorem measurableSet_chart_of_isOpen (A : FinHolAtlas D X) {S : Set X} (hS : IsOpen S) (j : Fin A.n) :
    MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) :=
  ((A.chart j).isOpen_inter_preimage_symm hS).measurableSet

/- English proof (translation)
Establish `h : (A.chart j).target ∩ (A.chart j).symm ⁻¹' (S \ S') = ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) \ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S')`. Use extensionality with `y`. Simplify using `only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_sdiff]`. The claim follows by propositional logic. Rewrite using `[h]`.

Conclude with `hS.diff hS'`.
-/
theorem measurableSet_chart_diff (A : FinHolAtlas D X) {S S' : Set X} (j : Fin A.n)
    (hS : MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S))
    (hS' : MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S')) :
    MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (S \ S')) := by
  have h : (A.chart j).target ∩ (A.chart j).symm ⁻¹' (S \ S') =
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) \
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S') := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_sdiff]
    tauto
  rw [h]
  exact hS.diff hS'

/- English proof (translation)
Establish `h : (A.chart j).target ∩ (A.chart j).symm ⁻¹' Sᶜ = (A.chart j).target \ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S)`. Use extensionality with `y`. Simplify using `only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_sdiff]`. The claim follows by propositional logic. Rewrite using `[h]`.

Conclude with `(A.chart j).open_target.measurableSet.diff hS`.
-/
theorem measurableSet_chart_compl (A : FinHolAtlas D X) {S : Set X} (j : Fin A.n)
    (hS : MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S)) :
    MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Sᶜ) := by
  have h : (A.chart j).target ∩ (A.chart j).symm ⁻¹' Sᶜ =
      (A.chart j).target \ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_sdiff]
    tauto
  rw [h]
  exact (A.chart j).open_target.measurableSet.diff hS

/- English proof (translation)
Introduce `j K hKt hK`. Establish `h1 : IntegrableOn (locDens A Ψ j) K` using `((ReciprocityTheory.AnForm.M.locDensCont A Ψ hΨ j).mono hKt).integrableOn_compact hK`. Use `(h1.indicator (hS j)).congr_fun (fun y hy => ?_) hK.measurableSet` and prove the remaining obligations. Distinguish the cases in `h : (A.chart j).symm y ∈ S`. Simplify using `[h, hKt hy]`.

Simplify using `[h]`.
-/
theorem mIntegrable_indicator (A : FinHolAtlas D X) (Ψ : Fin D → LocPot X)
    (hΨ : ∀ i, IsPotential A (Ψ i)) (S : Set X)
    (hS : ∀ j, MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S)) :
    MIntegrable A Ψ (S.indicator 1) := by
  intro j K hKt hK
  have h1 : IntegrableOn (locDens A Ψ j) K :=
    ((ReciprocityTheory.AnForm.M.locDensCont A Ψ hΨ j).mono hKt).integrableOn_compact hK
  refine (h1.indicator (hS j)).congr_fun (fun y hy => ?_) hK.measurableSet
  by_cases h : (A.chart j).symm y ∈ S
  · simp [h, hKt hy]
  · simp [h]

/- English proof (translation)
Establish `h` using `ReciprocityTheory.AnForm.M.mIntLinear A Ψ hΨ 1 _ _ (mIntegrable_indicator A Ψ hΨ S hS) (mIntegrable_indicator A Ψ hΨ S' hS')`. Rewrite `h` using `[one_mul]`. Rewrite using `[← h]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Rewrite using `[Set.indicator_union_of_disjoint hd, one_mul]`.
-/
theorem mInt_indicator_union [CompactSpace X] [T2Space X] (A : FinHolAtlas D X)
    (Ψ : Fin D → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) (S S' : Set X)
    (hS : ∀ j, MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S))
    (hS' : ∀ j, MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S'))
    (hd : Disjoint S S') :
    mInt A Ψ ((S ∪ S').indicator 1) = mInt A Ψ (S.indicator 1) + mInt A Ψ (S'.indicator 1) := by
  have h := ReciprocityTheory.AnForm.M.mIntLinear A Ψ hΨ 1 _ _ (mIntegrable_indicator A Ψ hΨ S hS)
    (mIntegrable_indicator A Ψ hΨ S' hS')
  rw [one_mul] at h
  rw [← h]
  congr 1
  funext x
  rw [Set.indicator_union_of_disjoint hd, one_mul]

/- English proof (translation)
Establish `h` using `mInt_indicator_union A Ψ hΨ S Sᶜ hS (fun j => measurableSet_chart_compl A j (hS j)) disjoint_compl_right`. Rewrite `h` using `[Set.union_compl_self, Set.indicator_univ]`. Conclude with `h`.
-/
theorem mInt_one_split [CompactSpace X] [T2Space X] (A : FinHolAtlas D X)
    (Ψ : Fin D → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) (S : Set X)
    (hS : ∀ j, MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S)) :
    mInt A Ψ (fun _ => 1) = mInt A Ψ (S.indicator 1) + mInt A Ψ (Sᶜ.indicator 1) := by
  have h := mInt_indicator_union A Ψ hΨ S Sᶜ hS (fun j => measurableSet_chart_compl A j (hS j))
    disjoint_compl_right
  rw [Set.union_compl_self, Set.indicator_univ] at h
  exact h

/- English proof (translation)
Establish `hKc : IsCompact ((A.chart j).symm '' K)` using `hK.image_of_continuousOn ((A.chart j).continuousOn_symm.mono hKt)`. Establish `hKs : (A.chart j).symm '' K ⊆ (A.chart j).source`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `(A.chart j).map_target (hKt hy)`. Take `⟨U, hU, hKU, hUs⟩` from `normal_exists_closure_subset hKc.isClosed (A.chart j).open_source hKs`.

Take `⟨f, hf1, hf0, -, hf01⟩` from `exists_continuous_one_zero_of_isCompact hKc hU.isClosed_compl (disjoint_compl_right.mono_left hKU)`. Establish `hts : tsupport f ⊆ (A.chart j).source`. Use `(closure_mono fun x hx => ?_).trans hUs` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hx (hf0 h)`.

Establish `hint : MIntegrable A Ψ f` using `ReciprocityTheory.AnForm.M.mIntegrableCont A Ψ hΨ f f.continuous`. Establish `hint' : MIntegrable A Ψ (fun x => 1 - f x)` using `ReciprocityTheory.AnForm.M.mIntegrableCont A Ψ hΨ _ (continuous_const.sub f.continuous)`. Establish `hne` using `ReciprocityTheory.AnForm.M.existsPartition A`. Establish `hloc : mInt A Ψ f = ∫ y in (A.chart j).target, f ((A.chart j).symm y) * locDens A Ψ j y`. Rewrite using `[ReciprocityTheory.AnForm.M.mIntEq A hne.some Ψ hΨ f hint]`.

Conclude with `ReciprocityTheory.AnForm.M.mIntLocalize A hne.some Ψ hΨ j f hts hint`. Establish `hT : IntegrableOn (fun y => f ((A.chart j).symm y) * locDens A Ψ j y) (A.chart j).target`. Take `⟨hc, hsub⟩` from `ReciprocityTheory.AnForm.M.image_closed_compact (A.chart j) (isClosed_tsupport f) hts`. Use `ReciprocityTheory.AnForm.M.integrableOn_target_of_closed (A.chart j) (Z := tsupport f) (fun y _ hy => ?_) (hint j _ hsub hc)` and prove the remaining obligations. Rewrite using `[image_eq_zero_of_notMem_tsupport hy, zero_mul]`.

Establish `h1 : ∫ y in K, locDens A Ψ j y ≤ mInt A Ψ f`. Rewrite using `[hloc]`. Combine the equalities or inequalities in the displayed calculation. Use `setIntegral_congr_fun hK.measurableSet fun y hy => ?_` and prove the remaining obligations. Simplify using `[hf1 ⟨y, hy, rfl⟩]`.

Use `_ ≤ _ := by`. Use `setIntegral_mono_set hT ?_ hKt.eventuallyLE` and prove the remaining obligations. Use `filter_upwards [ae_restrict_mem (A.chart j).open_target.measurableSet] with y hy`. Conclude with `mul_nonneg (hf01 _).1 (ReciprocityTheory.AnForm.M.locDens_nonneg_of_psh A Ψ hΨ hpsh j hy)`. Establish `h2` using `ReciprocityTheory.AnForm.M.mIntLinear A Ψ hΨ 1 _ _ hint hint'`.

Establish `h3 : (fun x => 1 * f x + (1 - f x)) = fun _ : X => (1 : ℝ)` using `funext fun x => by ring`. Rewrite `h2` using `[h3]`. Establish `h4` using `ReciprocityTheory.AnForm.M.mIntNonneg A Ψ hΨ hpsh (fun x => 1 - f x) fun x => sub_nonneg.2 (hf01 x).2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem setIntegral_locDens_le_mInt [CompactSpace X] [T2Space X] (A : FinHolAtlas D X)
    (Ψ : Fin D → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) (hpsh : ∀ i, IsPsh A (Ψ i))
    (j : Fin A.n) (K : Set (Fin D → ℂ)) (hKt : K ⊆ (A.chart j).target) (hK : IsCompact K) :
    ∫ y in K, locDens A Ψ j y ≤ mInt A Ψ (fun _ => 1) := by
  have hKc : IsCompact ((A.chart j).symm '' K) :=
    hK.image_of_continuousOn ((A.chart j).continuousOn_symm.mono hKt)
  have hKs : (A.chart j).symm '' K ⊆ (A.chart j).source := by
    rintro _ ⟨y, hy, rfl⟩
    exact (A.chart j).map_target (hKt hy)
  obtain ⟨U, hU, hKU, hUs⟩ := normal_exists_closure_subset hKc.isClosed (A.chart j).open_source hKs
  obtain ⟨f, hf1, hf0, -, hf01⟩ := exists_continuous_one_zero_of_isCompact hKc hU.isClosed_compl
    (disjoint_compl_right.mono_left hKU)
  have hts : tsupport f ⊆ (A.chart j).source := by
    refine (closure_mono fun x hx => ?_).trans hUs
    by_contra h
    exact hx (hf0 h)
  have hint : MIntegrable A Ψ f := ReciprocityTheory.AnForm.M.mIntegrableCont A Ψ hΨ f f.continuous
  have hint' : MIntegrable A Ψ (fun x => 1 - f x) :=
    ReciprocityTheory.AnForm.M.mIntegrableCont A Ψ hΨ _ (continuous_const.sub f.continuous)
  have hne := ReciprocityTheory.AnForm.M.existsPartition A
  have hloc : mInt A Ψ f = ∫ y in (A.chart j).target, f ((A.chart j).symm y) * locDens A Ψ j y := by
    rw [ReciprocityTheory.AnForm.M.mIntEq A hne.some Ψ hΨ f hint]
    exact ReciprocityTheory.AnForm.M.mIntLocalize A hne.some Ψ hΨ j f hts hint
  have hT : IntegrableOn (fun y => f ((A.chart j).symm y) * locDens A Ψ j y) (A.chart j).target := by
    obtain ⟨hc, hsub⟩ := ReciprocityTheory.AnForm.M.image_closed_compact (A.chart j) (isClosed_tsupport f) hts
    refine ReciprocityTheory.AnForm.M.integrableOn_target_of_closed (A.chart j) (Z := tsupport f)
      (fun y _ hy => ?_) (hint j _ hsub hc)
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  have h1 : ∫ y in K, locDens A Ψ j y ≤ mInt A Ψ f := by
    rw [hloc]
    calc ∫ y in K, locDens A Ψ j y
        = ∫ y in K, f ((A.chart j).symm y) * locDens A Ψ j y := by
          refine setIntegral_congr_fun hK.measurableSet fun y hy => ?_
          simp [hf1 ⟨y, hy, rfl⟩]
      _ ≤ _ := by
          refine setIntegral_mono_set hT ?_ hKt.eventuallyLE
          filter_upwards [ae_restrict_mem (A.chart j).open_target.measurableSet] with y hy
          exact mul_nonneg (hf01 _).1
            (ReciprocityTheory.AnForm.M.locDens_nonneg_of_psh A Ψ hΨ hpsh j hy)
  have h2 := ReciprocityTheory.AnForm.M.mIntLinear A Ψ hΨ 1 _ _ hint hint'
  have h3 : (fun x => 1 * f x + (1 - f x)) = fun _ : X => (1 : ℝ) := funext fun x => by ring
  rw [h3] at h2
  have h4 := ReciprocityTheory.AnForm.M.mIntNonneg A Ψ hΨ hpsh (fun x => 1 - f x)
    fun x => sub_nonneg.2 (hf01 x).2
  linarith

/- English proof (translation)
Use `⟨aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hG n).1) hlim, ?_⟩` and prove the remaining obligations. Establish `hF : ∫⁻ x, ‖F x‖ₑ ∂μ ≤ liminf (fun n => ∫⁻ x, ‖G n x‖ₑ ∂μ) atTop` using `lintegral_congr_ae (by filter_upwards [hlim] with x hx using hx.enorm.liminf_eq) ▸ lintegral_liminf_le' (fun n => (hG n).1.aemeasurable.enorm)`. Establish `hb : ∀ n, ∫⁻ x, ‖G n x‖ₑ ∂μ ≤ ENNReal.ofReal C`. Introduce `n`. Establish `h1 : ∫⁻ x, ‖G n x‖ₑ ∂μ = ENNReal.ofReal (∫ x, G n x ∂μ)`.

Rewrite using `[ofReal_integral_eq_lintegral_ofReal (hG n) (h0 n)]`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [h0 n] with x hx`. Conclude with `Real.enorm_eq_ofReal hx`. Rewrite using `[h1]`.

Conclude with `ENNReal.ofReal_le_ofReal (hC n)`. Conclude with `(hF.trans (liminf_le_of_frequently_le' (Frequently.of_forall hb))).trans_lt ENNReal.ofReal_lt_top`.
-/
theorem integrable_of_tendsto_of_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {G : ℕ → α → ℝ} {F : α → ℝ} (hG : ∀ n, Integrable (G n) μ) (h0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ G n x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => G n x) atTop (𝓝 (F x))) (C : ℝ)
    (hC : ∀ n, ∫ x, G n x ∂μ ≤ C) : Integrable F μ := by
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hG n).1) hlim, ?_⟩
  have hF : ∫⁻ x, ‖F x‖ₑ ∂μ ≤ liminf (fun n => ∫⁻ x, ‖G n x‖ₑ ∂μ) atTop :=
    lintegral_congr_ae (by filter_upwards [hlim] with x hx using hx.enorm.liminf_eq) ▸
      lintegral_liminf_le' (fun n => (hG n).1.aemeasurable.enorm)
  have hb : ∀ n, ∫⁻ x, ‖G n x‖ₑ ∂μ ≤ ENNReal.ofReal C := by
    intro n
    have h1 : ∫⁻ x, ‖G n x‖ₑ ∂μ = ENNReal.ofReal (∫ x, G n x ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal (hG n) (h0 n)]
      refine lintegral_congr_ae ?_
      filter_upwards [h0 n] with x hx
      exact Real.enorm_eq_ofReal hx
    rw [h1]
    exact ENNReal.ofReal_le_ofReal (hC n)
  exact (hF.trans (liminf_le_of_frequently_le' (Frequently.of_forall hb))).trans_lt
    ENNReal.ofReal_lt_top

end

end GroundTheory.Heights₂.Heights.AnalyticLimit

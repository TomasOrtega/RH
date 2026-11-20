import Mathlib
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.RightInvariantOfCovolume

noncomputable section
open MeasureTheory
open scoped Pointwise Topology ENNReal
namespace GlobalTheory.LatticeQuotUniq
open GlobalTheory.AutQuotCheck

section Alg
variable {G : Type} [Group G] [MeasurableSpace G] (Γ : Subgroup G)

def fibreMeasure (q : Quotient (QuotientGroup.rightRel Γ)) : Measure G :=
  Quotient.lift (fun g : G => Measure.sum fun γ : Γ => Measure.dirac ((γ : G) * g)) (by
    intro a b hab
    obtain ⟨δ, hδ, rfl⟩ := (cls_eq_iff Γ a b).1 (Quotient.sound hab)
    have := Measure.sum_comp_equiv (Equiv.mulRight (⟨δ, hδ⟩ : Γ))
      (fun γ : Γ => Measure.dirac ((γ : G) * a))
    rw [← this]
    congr 1
    ext1 γ
    simp [mul_assoc]) q

/- English proof (translation)
Use `show (Measure.sum fun γ : Γ => Measure.dirac ((γ : G) * g)) A = _`. Rewrite using `[Measure.sum_apply _ hA]`. Simplify using `only [Measure.dirac_apply' _ hA]`.
-/
theorem fibreMeasure_apply (g : G) {A : Set G} (hA : MeasurableSet A) :
    fibreMeasure Γ (cls Γ g) A = ∑' γ : Γ, A.indicator (1 : G → ℝ≥0∞) ((γ : G) * g) := by
  show (Measure.sum fun γ : Γ => Measure.dirac ((γ : G) * g)) A = _
  rw [Measure.sum_apply _ hA]
  simp only [Measure.dirac_apply' _ hA]

/- English proof (translation)
Use `Measure.measurable_of_measurable_coe _ fun A hA => ?_` and prove the remaining obligations. Use `measurable_from_quotient.2 ?_` and prove the remaining obligations. Establish `: ((fun q => fibreMeasure Γ q A) ∘ Quotient.mk'') = fun g : G => ∑' γ : Γ, A.indicator (1 : G → ℝ≥0∞) ((γ : G) * g)`. Use extensionality with `g`. Conclude with `fibreMeasure_apply Γ g hA`.

Rewrite using `[this]`. Conclude with `Measurable.ennreal_tsum fun γ => (measurable_one.indicator hA).comp (measurable_const_mul _)`.
-/
theorem measurable_fibreMeasure [MeasurableMul G] [Countable Γ] : Measurable (fibreMeasure Γ) := by
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  refine measurable_from_quotient.2 ?_
  have : ((fun q => fibreMeasure Γ q A) ∘ Quotient.mk'') =
      fun g : G => ∑' γ : Γ, A.indicator (1 : G → ℝ≥0∞) ((γ : G) * g) := by
    ext g; exact fibreMeasure_apply Γ g hA
  rw [this]
  exact Measurable.ennreal_tsum fun γ =>
    (measurable_one.indicator hA).comp (measurable_const_mul _)

/- English proof (translation)
Proceed by induction on `q using Quotient.inductionOn with`. Consider the case `h g`. Rewrite using `[show fibreMeasure Γ (Quotient.mk _ g) A = _ from fibreMeasure_apply Γ g hA]`. Distinguish the cases in `hg : (Quotient.mk _ g) ∈ cls Γ '' A`. Rewrite using `[Set.indicator_of_mem hg]`.

Take `⟨a, ha, hag⟩` from `hg`. Take `⟨δ, hδ, rfl⟩` from `(cls_eq_iff Γ g a).1 hag.symm`. Rewrite using `[tsum_eq_single (⟨δ, hδ⟩ : Γ)]`. Simplify using `[Set.indicator_of_mem ha]`. Introduce `γ hγ`.

Use `Set.indicator_of_notMem (fun hm => hγ ?_) _` and prove the remaining obligations. Use `h (γ * (⟨δ, hδ⟩ : Γ)⁻¹) _ ha (by simpa [mul_assoc] using hm)` as an intermediate fact. Conclude with `mul_inv_eq_one.1 this`. Rewrite using `[Set.indicator_of_notMem hg]`. Use `ENNReal.tsum_eq_zero.2 fun γ => Set.indicator_of_notMem (fun hm => hg ?_) _` and prove the remaining obligations.

Conclude with `⟨_, hm, cls_smul Γ γ g⟩`.
-/
theorem fibreMeasure_of_injOn {A : Set G} (hA : MeasurableSet A)
    (h : ∀ γ : Γ, ∀ x ∈ A, (γ : G) * x ∈ A → γ = 1) (q : Quotient (QuotientGroup.rightRel Γ)) :
    fibreMeasure Γ q A = (cls Γ '' A).indicator 1 q := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [show fibreMeasure Γ (Quotient.mk _ g) A = _ from fibreMeasure_apply Γ g hA]
    by_cases hg : (Quotient.mk _ g) ∈ cls Γ '' A
    · rw [Set.indicator_of_mem hg]
      obtain ⟨a, ha, hag⟩ := hg
      obtain ⟨δ, hδ, rfl⟩ := (cls_eq_iff Γ g a).1 hag.symm
      rw [tsum_eq_single (⟨δ, hδ⟩ : Γ)]
      · simp [Set.indicator_of_mem ha]
      · intro γ hγ
        refine Set.indicator_of_notMem (fun hm => hγ ?_) _
        have := h (γ * (⟨δ, hδ⟩ : Γ)⁻¹) _ ha (by simpa [mul_assoc] using hm)
        exact mul_inv_eq_one.1 this
    · rw [Set.indicator_of_notMem hg]
      refine ENNReal.tsum_eq_zero.2 fun γ => Set.indicator_of_notMem (fun hm => hg ?_) _
      exact ⟨_, hm, cls_smul Γ γ g⟩

/- English proof (translation)
Proceed by induction on `q using Quotient.inductionOn with`. Consider the case `h g`. Rewrite using `[show fibreMeasure Γ (Quotient.mk _ g) _ = _ from fibreMeasure_apply Γ g (measurable_cls Γ hs)]`. Use `le_trans ?_ (ENNReal.le_tsum (1 : Γ))` and prove the remaining obligations. Distinguish the cases in `hg : (Quotient.mk _ g) ∈ s`.

Rewrite using `[Set.indicator_of_mem hg, Set.indicator_of_mem (by simpa using hg)]; simp`. Rewrite using `[Set.indicator_of_notMem hg]`. Conclude with `zero_le`.
-/
theorem indicator_le_fibreMeasure {s : Set (Quotient (QuotientGroup.rightRel Γ))} (hs : MeasurableSet s)
    (q : Quotient (QuotientGroup.rightRel Γ)) :
    s.indicator 1 q ≤ fibreMeasure Γ q (cls Γ ⁻¹' s) := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [show fibreMeasure Γ (Quotient.mk _ g) _ = _ from fibreMeasure_apply Γ g (measurable_cls Γ hs)]
    refine le_trans ?_ (ENNReal.le_tsum (1 : Γ))
    by_cases hg : (Quotient.mk _ g) ∈ s
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (by simpa using hg)]; simp
    · rw [Set.indicator_of_notMem hg]; exact zero_le

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, h⟩`. Take `⟨δ, hδ, rfl⟩` from `(cls_eq_iff Γ x a).1 h.symm`.

Conclude with `⟨⟨δ, hδ⟩, ha⟩`. Introduce and unpack `⟨γ, h⟩`. Conclude with `⟨_, h, cls_smul Γ γ x⟩`.
-/
theorem preimage_image_cls (A : Set G) :
    cls Γ ⁻¹' (cls Γ '' A) = ⋃ γ : Γ, (fun x => (γ : G) * x) ⁻¹' A := by
  ext x
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
  constructor
  · rintro ⟨a, ha, h⟩
    obtain ⟨δ, hδ, rfl⟩ := (cls_eq_iff Γ x a).1 h.symm
    exact ⟨⟨δ, hδ⟩, ha⟩
  · rintro ⟨γ, h⟩
    exact ⟨_, h, cls_smul Γ γ x⟩

/- English proof (translation)
Use `show MeasurableSet (cls Γ ⁻¹' (cls Γ '' A))`. Rewrite using `[preimage_image_cls]`. Conclude with `MeasurableSet.iUnion fun γ => measurable_const_mul _ hA`.
-/
theorem measurableSet_image_cls [MeasurableMul G] [Countable Γ] {A : Set G} (hA : MeasurableSet A) :
    MeasurableSet (cls Γ '' A) := by
  show MeasurableSet (cls Γ ⁻¹' (cls Γ '' A))
  rw [preimage_image_cls]
  exact MeasurableSet.iUnion fun γ => measurable_const_mul _ hA

/- English proof (translation)
Take `⟨E, hsub, hE, hae⟩` from `hF.fundamentalInterior.nullMeasurableSet.exists_measurable_subset_ae_eq`. Establish `h2 : fundamentalInterior Γ F =ᵐ[μ] F`. Rewrite using `[← sdiff_fundamentalFrontier]`. Conclude with `diff_ae_eq_self.2 (measure_mono_null Set.inter_subset_right hF.measure_fundamentalFrontier)`. Establish `h3` using `hae.trans h2`.

Use `⟨E, hE, h3, ?_, ?_⟩` and prove the remaining obligations. Introduce `γ x hx hγ`. Assume the negation of the conclusion as `hne`. Use `(mem_fundamentalInterior.1 (hsub hγ)).2 γ hne` as an intermediate fact. Conclude with `this ⟨x, fundamentalInterior_subset (hsub hx), rfl⟩`.

Rewrite using `[Set.preimage_compl, preimage_image_cls]`. Establish `h4 : ∀ᵐ x ∂μ, ∀ γ : Γ, ((γ : G) * x ∈ F → (γ : G) * x ∈ E)`. Use `ae_all_iff.2 fun γ => ?_` and prove the remaining obligations. Conclude with `(measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving.ae h3.symm.le`. Establish `h5 : ∀ᵐ x ∂μ, x ∈ ⋃ γ : Γ, (fun x => (γ : G) * x) ⁻¹' E` using `by filter_upwards [h4, hF.ae_covers] with x hx ⟨γ, hγ⟩`.

Conclude with `Set.mem_iUnion.2 ⟨γ, hx γ hγ⟩`. Conclude with `h5`.
-/
theorem exists_strict_domain [MeasurableMul G] [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    {F : Set G} (hF : IsFundamentalDomain Γ F μ) :
    ∃ E : Set G, MeasurableSet E ∧ E =ᵐ[μ] F ∧ (∀ γ : Γ, ∀ x ∈ E, (γ : G) * x ∈ E → γ = 1) ∧
      μ (cls Γ ⁻¹' (cls Γ '' E)ᶜ) = 0 := by
  obtain ⟨E, hsub, hE, hae⟩ := hF.fundamentalInterior.nullMeasurableSet.exists_measurable_subset_ae_eq
  have h2 : fundamentalInterior Γ F =ᵐ[μ] F := by
    rw [← sdiff_fundamentalFrontier]
    exact diff_ae_eq_self.2 (measure_mono_null Set.inter_subset_right hF.measure_fundamentalFrontier)
  have h3 := hae.trans h2
  refine ⟨E, hE, h3, ?_, ?_⟩
  · intro γ x hx hγ
    by_contra hne
    have := (mem_fundamentalInterior.1 (hsub hγ)).2 γ hne
    exact this ⟨x, fundamentalInterior_subset (hsub hx), rfl⟩
  · rw [Set.preimage_compl, preimage_image_cls]
    have h4 : ∀ᵐ x ∂μ, ∀ γ : Γ, ((γ : G) * x ∈ F → (γ : G) * x ∈ E) := by
      refine ae_all_iff.2 fun γ => ?_
      exact (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving.ae h3.symm.le
    have h5 : ∀ᵐ x ∂μ, x ∈ ⋃ γ : Γ, (fun x => (γ : G) * x) ⁻¹' E := by
      filter_upwards [h4, hF.ae_covers] with x hx ⟨γ, hγ⟩
      exact Set.mem_iUnion.2 ⟨γ, hx γ hγ⟩
    exact h5

end Alg

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ Γ _ μ _ F hF hfin ν _ hinv`. Establish `h0 : μ F ≠ 0` using `hF.measure_ne_zero (NeZero.ne μ)`. Use `haveI : μ.IsMulRightInvariant := ⟨rightInvariant_of_covolume Γ μ hF h0 hfin⟩`. Take `⟨E, hE, hEF, hEs, hEn⟩` from `exists_strict_domain Γ μ hF`. Establish `hκ` using `measurable_fibreMeasure Γ`.

Use `set L : Measure G := ν.bind (fibreMeasure Γ) with hL`. Establish `hLa : ∀ A, MeasurableSet A → L A = ∫⁻ q, fibreMeasure Γ q A ∂ν` using `fun A hA => Measure.bind_apply hA hκ.aemeasurable`. Establish `hLi : ∀ A, MeasurableSet A → (∀ γ : Γ, ∀ x ∈ A, (γ : G) * x ∈ A → γ = 1) → L A = ν (cls Γ '' A)`. Introduce `A hA h`. Rewrite using `[hLa A hA]`.

Repeatedly rewrite using `[fibreMeasure_of_injOn Γ hA h]`. Conclude with `lintegral_indicator_one (measurableSet_image_cls Γ hA)`. Use `haveI : L.IsMulRightInvariant := by`. Use `⟨fun h => ?_⟩` and prove the remaining obligations. Set `ρ : Quotient (QuotientGroup.rightRel Γ) → Quotient (QuotientGroup.rightRel Γ)` to `Quotient.lift (fun g => cls Γ (g * h)) (by`.

Introduce `a b hab`. Take `⟨δ, hδ, rfl⟩` from `(cls_eq_iff Γ a b).1 (Quotient.sound hab)`. Conclude with `(cls_eq_iff Γ _ _).2 ⟨δ, hδ, mul_assoc _ _ _⟩)`. Establish `hρ : Measurable ρ` using `measurable_from_quotient.2 ((measurable_cls Γ).comp (measurable_mul_const h))`. Establish `hmp : MeasurePreserving ρ ν ν` using `⟨hρ, by`.

Use extensionality with `s hs`. Rewrite using `[Measure.map_apply hρ hs]`. Conclude with `hinv h ρ (fun _ => rfl) s hs⟩`. Use extensionality with `A hA`. Rewrite using `[Measure.map_apply (measurable_mul_const h) hA, hLa _ (measurable_mul_const h hA), hLa _ hA, ← hmp.lintegral_comp (f := fun q => fibreMeasure Γ q A) ((Measure.measurable_coe hA).comp hκ)]`.

Use `lintegral_congr fun q => ?_` and prove the remaining obligations. Proceed by induction on `q using Quotient.inductionOn with`. Consider the case `h g`. Use `(fibreMeasure_apply Γ g (measurable_mul_const h hA)).trans (Eq.trans ?_ (fibreMeasure_apply Γ (g * h) hA).symm)` and prove the remaining obligations. Use `tsum_congr fun γ => ?_` and prove the remaining obligations.

Rewrite using `[← mul_assoc]`. Both sides reduce to the same expression. Use `haveI : IsLocallyFiniteMeasure L := by`. Establish `hpos : 0 < μ E` using `by rw [measure_congr hEF]; exact pos_iff_ne_zero.2 h0`. Establish `hn` using `Measure.div_mem_nhds_one_of_haar_pos μ E hE hpos`.

Use `⟨fun g => ?_⟩` and prove the remaining obligations. Establish `hc : ContinuousAt (fun p : G × G => p.1 / p.2) (g, g)` using `continuous_div'.continuousAt`. Establish `h1 : (fun p : G × G => p.1 / p.2) ⁻¹' (E / E) ∈ 𝓝 (g, g)` using `hc (by simpa using hn)`. Take `⟨U, hU, V, hV, hUV⟩` from `mem_nhds_prod_iff.1 h1`. Take `⟨W, hW, hWo, hgW⟩` from `mem_nhds_iff.1 (Filter.inter_mem hU hV)`.

Use `⟨W, hWo.mem_nhds hgW, ?_⟩` and prove the remaining obligations. Rewrite using `[hLi W hWo.measurableSet]`. Conclude with `measure_lt_top _ _`. Introduce `γ x hx hγ`. Establish `: ((γ : G) * x) / x ∈ E / E` using `hUV (Set.mk_mem_prod (hW hγ).1 (hW hx).2)`.

Take `⟨a, ha, b, hb, hab⟩` from `this`. Use `hEs γ b hb ?_` and prove the remaining obligations. Establish `: a = (γ : G) * b`. Simplify using `only [mul_div_cancel_right] at hab`. Rewrite using `[← hab]`.

Simplify using the standard rewrite rules. Rewrite using `[← this]` and apply the resulting hypothesis. Use `haveI : μ.inv.IsHaarMeasure := {}`. Establish `e` using `Measure.isMulLeftInvariant_eq_smul L.inv μ.inv`. Use `set c := Measure.haarScalarFactor L.inv μ.inv`.

Establish `e2 : L = (c : ℝ≥0∞) • μ`. Use `congrArg Measure.inv e` as an intermediate fact. Rewrite `this` using `[Measure.inv_inv]`. Rewrite using `[this]`. Use `show Measure.map _ _ = _`.

Rewrite using `[Measure.map_smul]`. Conclude with `congrArg (c • ·) (Measure.inv_inv μ)`. Establish `hT` using `measurableSet_image_cls Γ hE`. Establish `hnull : ν (cls Γ '' E)ᶜ = 0`. Use `le_antisymm ?_ zero_le` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Establish `key : ν = (c : ℝ≥0∞) • (μ.restrict F).map (cls Γ)`. Use extensionality with `s hs`. Rewrite using `[Measure.smul_apply, Measure.map_apply (measurable_cls Γ) hs, ← Measure.restrict_congr_set hEF, Measure.restrict_apply (measurable_cls Γ hs), ← Measure.smul_apply, ← e2, hLi _ ((measurable_cls Γ hs).inter hE) (fun γ x hx hγ => hEs γ x hx.2 hγ.2), Set.image_preimage_inter]`. Conclude with `(measure_inter_conull hnull).symm`.

Establish `h1 : (c : ℝ≥0∞) * μ F = 1`. Use `congrArg (fun m => m Set.univ) key` as an intermediate fact. Simplify using `only [measure_univ, Measure.smul_apply, smul_eq_mul] at this`. Rewrite `this` using `[Measure.map_apply (measurable_cls Γ) MeasurableSet.univ]`. Simplify using `using this.symm`.

Rewrite using `[← ENNReal.eq_inv_of_mul_eq_one_left h1]`. Conclude with `key`.
-/
theorem invariant_prob_eq : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 ≠ ⊤ → ∀ (ν : Measure (Quotient (QuotientGroup.rightRel Γ))) [IsProbabilityMeasure ν], (∀ (h : G) (ρ : Quotient (QuotientGroup.rightRel Γ) → Quotient (QuotientGroup.rightRel Γ)), (∀ g : G, ρ (Quotient.mk _ g) = Quotient.mk _ (g * h)) → ∀ s, MeasurableSet s → ν (ρ ⁻¹' s) = ν s) → ν = (μ 𝓕)⁻¹ • (μ.restrict 𝓕).map (fun g : G => (Quotient.mk _ g : Quotient (QuotientGroup.rightRel Γ))) := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ F hF hfin ν _ hinv
  have h0 : μ F ≠ 0 := hF.measure_ne_zero (NeZero.ne μ)
  haveI : μ.IsMulRightInvariant := ⟨rightInvariant_of_covolume Γ μ hF h0 hfin⟩
  obtain ⟨E, hE, hEF, hEs, hEn⟩ := exists_strict_domain Γ μ hF
  have hκ := measurable_fibreMeasure Γ
  set L : Measure G := ν.bind (fibreMeasure Γ) with hL
  have hLa : ∀ A, MeasurableSet A → L A = ∫⁻ q, fibreMeasure Γ q A ∂ν :=
    fun A hA => Measure.bind_apply hA hκ.aemeasurable
  have hLi : ∀ A, MeasurableSet A → (∀ γ : Γ, ∀ x ∈ A, (γ : G) * x ∈ A → γ = 1) →
      L A = ν (cls Γ '' A) := by
    intro A hA h
    rw [hLa A hA]
    simp_rw [fibreMeasure_of_injOn Γ hA h]
    exact lintegral_indicator_one (measurableSet_image_cls Γ hA)
  haveI : L.IsMulRightInvariant := by
    refine ⟨fun h => ?_⟩
    let ρ : Quotient (QuotientGroup.rightRel Γ) → Quotient (QuotientGroup.rightRel Γ) :=
      Quotient.lift (fun g => cls Γ (g * h)) (by
        intro a b hab
        obtain ⟨δ, hδ, rfl⟩ := (cls_eq_iff Γ a b).1 (Quotient.sound hab)
        exact (cls_eq_iff Γ _ _).2 ⟨δ, hδ, mul_assoc _ _ _⟩)
    have hρ : Measurable ρ :=
      measurable_from_quotient.2 ((measurable_cls Γ).comp (measurable_mul_const h))
    have hmp : MeasurePreserving ρ ν ν := ⟨hρ, by
      ext s hs
      rw [Measure.map_apply hρ hs]
      exact hinv h ρ (fun _ => rfl) s hs⟩
    ext A hA
    rw [Measure.map_apply (measurable_mul_const h) hA, hLa _ (measurable_mul_const h hA), hLa _ hA,
      ← hmp.lintegral_comp (f := fun q => fibreMeasure Γ q A) ((Measure.measurable_coe hA).comp hκ)]
    refine lintegral_congr fun q => ?_
    induction q using Quotient.inductionOn with
    | h g =>
      refine (fibreMeasure_apply Γ g (measurable_mul_const h hA)).trans
        (Eq.trans ?_ (fibreMeasure_apply Γ (g * h) hA).symm)
      refine tsum_congr fun γ => ?_
      rw [← mul_assoc]
      rfl
  haveI : IsLocallyFiniteMeasure L := by
    have hpos : 0 < μ E := by rw [measure_congr hEF]; exact pos_iff_ne_zero.2 h0
    have hn := Measure.div_mem_nhds_one_of_haar_pos μ E hE hpos
    refine ⟨fun g => ?_⟩
    have hc : ContinuousAt (fun p : G × G => p.1 / p.2) (g, g) := continuous_div'.continuousAt
    have h1 : (fun p : G × G => p.1 / p.2) ⁻¹' (E / E) ∈ 𝓝 (g, g) := hc (by simpa using hn)
    obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 h1
    obtain ⟨W, hW, hWo, hgW⟩ := mem_nhds_iff.1 (Filter.inter_mem hU hV)
    refine ⟨W, hWo.mem_nhds hgW, ?_⟩
    rw [hLi W hWo.measurableSet]
    · exact measure_lt_top _ _
    · intro γ x hx hγ
      have : ((γ : G) * x) / x ∈ E / E := hUV (Set.mk_mem_prod (hW hγ).1 (hW hx).2)
      obtain ⟨a, ha, b, hb, hab⟩ := this
      refine hEs γ b hb ?_
      have : a = (γ : G) * b := by
        simp only [mul_div_cancel_right] at hab
        rw [← hab]; simp
      rwa [← this]
  haveI : μ.inv.IsHaarMeasure := {}
  have e := Measure.isMulLeftInvariant_eq_smul L.inv μ.inv
  set c := Measure.haarScalarFactor L.inv μ.inv
  have e2 : L = (c : ℝ≥0∞) • μ := by
    have := congrArg Measure.inv e
    rw [Measure.inv_inv] at this
    rw [this]
    show Measure.map _ _ = _
    rw [Measure.map_smul]
    exact congrArg (c • ·) (Measure.inv_inv μ)
  have hT := measurableSet_image_cls Γ hE
  have hnull : ν (cls Γ '' E)ᶜ = 0 := by
    refine le_antisymm ?_ zero_le
    calc ν (cls Γ '' E)ᶜ = ∫⁻ q, (cls Γ '' E)ᶜ.indicator 1 q ∂ν := (lintegral_indicator_one hT.compl).symm
      _ ≤ _ := lintegral_mono fun q => indicator_le_fibreMeasure Γ hT.compl q
      _ = L _ := (hLa _ (measurable_cls Γ hT.compl)).symm
      _ = 0 := by rw [e2, Measure.smul_apply, hEn, smul_zero]
  have key : ν = (c : ℝ≥0∞) • (μ.restrict F).map (cls Γ) := by
    ext s hs
    rw [Measure.smul_apply, Measure.map_apply (measurable_cls Γ) hs, ← Measure.restrict_congr_set hEF,
      Measure.restrict_apply (measurable_cls Γ hs), ← Measure.smul_apply, ← e2,
      hLi _ ((measurable_cls Γ hs).inter hE) (fun γ x hx hγ => hEs γ x hx.2 hγ.2),
      Set.image_preimage_inter]
    exact (measure_inter_conull hnull).symm
  have h1 : (c : ℝ≥0∞) * μ F = 1 := by
    have := congrArg (fun m => m Set.univ) key
    simp only [measure_univ, Measure.smul_apply, smul_eq_mul] at this
    rw [Measure.map_apply (measurable_cls Γ) MeasurableSet.univ] at this
    simpa using this.symm
  rw [← ENNReal.eq_inv_of_mul_eq_one_left h1]
  exact key

end GlobalTheory.LatticeQuotUniq

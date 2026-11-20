import ReciprocityTheory.L2DbarEstimates.NormFibrations.Hormander
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq
import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.HE

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal

noncomputable section

variable {n : ℕ} {U : Set (V n)}

/- English proof (translation)
The claim follows from `hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph`.
-/
theorem val_lh (hU : IsOpen U) : IsLocalHomeomorph (Subtype.val : U → V n) :=
  hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph

/- English proof (translation)
The claim follows from `(he (e.map_target hy)).trans (e.right_inv hy)`.
-/
theorem symm_val {e : OpenPartialHomeomorph U (V n)} (he : IsChart n (Subtype.val : U → V n) e)
    {y : V n} (hy : y ∈ e.target) : ((e.symm y : U) : V n) = y :=
  (he (e.map_target hy)).trans (e.right_inv hy)

/- English proof (translation)
Introduce `y hy` and use `by rw [← symm_val he hy] exact (e.symm y).2`.
-/
theorem target_sub {e : OpenPartialHomeomorph U (V n)} (he : IsChart n (Subtype.val : U → V n) e) :
    e.target ⊆ U := fun y hy => by
  rw [← symm_val he hy]
  exact (e.symm y).2

/- English proof (translation)
Introduce `y hy` and use `by simp only [Function.comp] rw [symm_val he hy]`.
-/
theorem comp_symm_eqOn (f : V n → ℂ) {e : OpenPartialHomeomorph U (V n)}
    (he : IsChart n (Subtype.val : U → V n) e) :
    Set.EqOn ((fun x : U => f x.1) ∘ e.symm) f e.target := fun y hy => by
  simp only [Function.comp]
  rw [symm_val he hy]

/- English proof (translation)
Introduce `e he` and use `(hf.mono (target_sub he)).congr (comp_symm_eqOn f he)`.
-/
theorem smooth_val {f : V n → ℂ} (hf : ContDiffOn ℝ ∞ f U) :
    Smooth n (Subtype.val : U → V n) (fun x => f x.1) := fun e he =>
  (hf.mono (target_sub he)).congr (comp_symm_eqOn f he)

/- English proof (translation)
The claim follows from `smooth_val (f := fun y => (f y : ℂ)) (Complex.ofRealCLM.contDiff.comp_contDiffOn hf)`.
-/
theorem smoothR_val {f : V n → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    SmoothR n (Subtype.val : U → V n) (fun x => f x.1) :=
  smooth_val (f := fun y => (f y : ℂ)) (Complex.ofRealCLM.contDiff.comp_contDiffOn hf)

/- English proof (translation)
Establish `hx' : x.1 ∈ e.target`. Rewrite using `[show x.1 = e x from he hx]`. Conclude with `e.map_source hx`. Conclude with `e.open_target.mem_nhds hx'`.
-/
theorem eventually_target (hU : IsOpen U) {e : OpenPartialHomeomorph U (V n)}
    (he : IsChart n (Subtype.val : U → V n) e) {x : U} (hx : x ∈ e.source) :
    e.target ∈ 𝓝 x.1 := by
  have hx' : x.1 ∈ e.target := by
    rw [show x.1 = e x from he hx]
    exact e.map_source hx
  exact e.open_target.mem_nhds hx'

/- English proof (translation)
Take `⟨e, he, hx⟩` from `exists_chart n (Subtype.val : U → V n) (val_lh hU) x`. Rewrite using `[levi_eq_leviV n _ e he _ x hx ξ]`. Conclude with `leviV_congr ((comp_symm_eqOn (fun y => (f y : ℂ)) he).eventuallyEq_of_mem (eventually_target hU he hx)) ξ`.
-/
theorem levi_val (hU : IsOpen U) (f : V n → ℝ) (x : U) (ξ : Fin n → ℂ) :
    Levi n (Subtype.val : U → V n) (fun y => f y.1) x ξ = leviV n (fun y => (f y : ℂ)) x.1 ξ := by
  obtain ⟨e, he, hx⟩ := exists_chart n (Subtype.val : U → V n) (val_lh hU) x
  rw [levi_eq_leviV n _ e he _ x hx ξ]
  exact leviV_congr ((comp_symm_eqOn (fun y => (f y : ℂ)) he).eventuallyEq_of_mem
    (eventually_target hU he hx)) ξ

/- English proof (translation)
Take `⟨e, he, hx⟩` from `exists_chart n (Subtype.val : U → V n) (val_lh hU) x`. Rewrite using `[db_eq_wdb n _ e he j _ x hx]`. Establish `hfe : ((fun y : U => f y.1) ∘ e.symm) =ᶠ[𝓝 x.1] f` using `(comp_symm_eqOn f he).eventuallyEq_of_mem (eventually_target hU he hx)`. Simplify using `only [wdb]`. Rewrite using `[hfe.fderiv_eq]`.
-/
theorem db_val (hU : IsOpen U) (f : V n → ℂ) (j : Fin n) (x : U) :
    db n (Subtype.val : U → V n) j (fun y => f y.1) x = wdb n j f x.1 := by
  obtain ⟨e, he, hx⟩ := exists_chart n (Subtype.val : U → V n) (val_lh hU) x
  rw [db_eq_wdb n _ e he j _ x hx]
  have hfe : ((fun y : U => f y.1) ∘ e.symm) =ᶠ[𝓝 x.1] f :=
    (comp_symm_eqOn f he).eventuallyEq_of_mem (eventually_target hU he hx)
  simp only [wdb]
  rw [hfe.fderiv_eq]

def ext0 (F : U → ℂ) (y : V n) : ℂ := by
  classical
  exact if h : y ∈ U then F ⟨y, h⟩ else 0

/- English proof (translation)
Simplify using `[ext0, x.2]`.
-/
theorem extendByZeroOnSubset_apply_coe (F : U → ℂ) (x : U) : ext0 F x.1 = F x := by
  simp [ext0, x.2]

/- English proof (translation)
Introduce `y hy`. Take `⟨e, he, hx⟩` from `exists_chart n (Subtype.val : U → V n) (val_lh hU) ⟨y, hy⟩`. Establish `hT : e.target ∈ 𝓝 y` using `eventually_target hU he hx`. Establish `hd : DifferentiableAt ℂ (F ∘ e.symm) y` using `(hF e he).differentiableAt hT`. Establish `heq : (F ∘ e.symm) =ᶠ[𝓝 y] ext0 F`.

Use `Filter.eventuallyEq_of_mem hT fun w hw => ?_` and prove the remaining obligations. Establish `h1` using `extendByZeroOnSubset_apply_coe F (e.symm w)`. Rewrite `h1` using `[symm_val he hw]`. Conclude with `h1.symm`. Conclude with `(hd.congr_of_eventuallyEq heq.symm).differentiableWithinAt`.
-/
theorem differentiableOn_extendByZero (hU : IsOpen U) {F : U → ℂ} (hF : Holo n (Subtype.val : U → V n) F) :
    DifferentiableOn ℂ (ext0 F) U := by
  intro y hy
  obtain ⟨e, he, hx⟩ := exists_chart n (Subtype.val : U → V n) (val_lh hU) ⟨y, hy⟩
  have hT : e.target ∈ 𝓝 y := eventually_target hU he hx
  have hd : DifferentiableAt ℂ (F ∘ e.symm) y := (hF e he).differentiableAt hT
  have heq : (F ∘ e.symm) =ᶠ[𝓝 y] ext0 F := by
    refine Filter.eventuallyEq_of_mem hT fun w hw => ?_
    have h1 := extendByZeroOnSubset_apply_coe F (e.symm w)
    rw [symm_val he hw] at h1
    exact h1.symm
  exact (hd.congr_of_eventuallyEq heq.symm).differentiableWithinAt

/- English proof (translation)
Establish `key : ∀ y : V n, ((A ∩ Subtype.val ⁻¹' {y}).encard : ℝ≥0∞) = (Subtype.val '' A).indicator 1 y`. Introduce `y`. Distinguish the cases in `hy : y ∈ Subtype.val '' A`. Take `⟨x, hxA, rfl⟩` from `hy`. Establish `hs : A ∩ Subtype.val ⁻¹' {x.1} = {x}`.

Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, hz⟩`. Conclude with `Set.mem_singleton_iff.mpr (Subtype.ext (Set.mem_singleton_iff.mp hz))`. Introduce `hz`.

Rewrite `hz` using `[Set.mem_singleton_iff]`. Substitute `hz` using the available equality. Conclude with `⟨hxA, rfl⟩`. Rewrite using `[hs, Set.encard_singleton, Set.indicator_of_mem (Set.mem_image_of_mem _ hxA)]`. Simplify using the standard rewrite rules.

Establish `hs : A ∩ Subtype.val ⁻¹' {y} = ∅`. Use extensionality with `z`. Simplify using `only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]`. Introduce `hz hzy`. Conclude with `hy ⟨z, hz, hzy⟩`.

Rewrite using `[hs, Set.encard_empty]`. Simplify using `[Set.indicator, hy]`. Rewrite using `[volFun, lintegral_congr key, lintegral_indicator_one (hU.measurableSet.subtype_image hA)]`.
-/
private theorem volFun_val_eq_volume_image (hU : IsOpen U) (A : Set U) (hA : MeasurableSet A) :
    volFun n (Subtype.val : U → V n) A = volume (Subtype.val '' A) := by
  have key : ∀ y : V n, ((A ∩ Subtype.val ⁻¹' {y}).encard : ℝ≥0∞) =
      (Subtype.val '' A).indicator 1 y := by
    intro y
    by_cases hy : y ∈ Subtype.val '' A
    · obtain ⟨x, hxA, rfl⟩ := hy
      have hs : A ∩ Subtype.val ⁻¹' {x.1} = {x} := by
        ext z
        constructor
        · rintro ⟨-, hz⟩
          exact Set.mem_singleton_iff.mpr (Subtype.ext (Set.mem_singleton_iff.mp hz))
        · intro hz
          rw [Set.mem_singleton_iff] at hz
          subst hz
          exact ⟨hxA, rfl⟩
      rw [hs, Set.encard_singleton, Set.indicator_of_mem (Set.mem_image_of_mem _ hxA)]
      simp
    · have hs : A ∩ Subtype.val ⁻¹' {y} = ∅ := by
        ext z
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro hz hzy
        exact hy ⟨z, hz, hzy⟩
      rw [hs, Set.encard_empty]
      simp [Set.indicator, hy]
  rw [volFun, lintegral_congr key, lintegral_indicator_one (hU.measurableSet.subtype_image hA)]

/- English proof (translation)
Establish `hadd : VolAdditive n (Subtype.val : U → V n)`. Introduce `f hf hd`. Rewrite using `[volFun_val_eq_volume_image hU _ (MeasurableSet.iUnion hf), Set.image_iUnion]`. Rewrite using `[measure_iUnion (fun i j hij => (hd hij).image Subtype.val_injective.injOn (Set.subset_univ _) (Set.subset_univ _)) (fun i => hU.measurableSet.subtype_image (hf i))]`. Conclude with `tsum_congr fun i => (volFun_val_eq_volume_image hU _ (hf i)).symm`.

Use extensionality with `A hA`. Rewrite using `[vol, dif_pos hadd, Measure.ofMeasurable_apply _ hA, Measure.comap_apply _ Subtype.val_injective (fun s hs => hU.measurableSet.subtype_image hs) _ hA]`. Conclude with `volFun_val_eq_volume_image hU A hA`.
-/
theorem vol_val (hU : IsOpen U) :
    vol n (Subtype.val : U → V n) = Measure.comap Subtype.val volume := by
  have hadd : VolAdditive n (Subtype.val : U → V n) := by
    intro f hf hd
    rw [volFun_val_eq_volume_image hU _ (MeasurableSet.iUnion hf), Set.image_iUnion]
    rw [measure_iUnion (fun i j hij => (hd hij).image Subtype.val_injective.injOn
      (Set.subset_univ _) (Set.subset_univ _)) (fun i => hU.measurableSet.subtype_image (hf i))]
    exact tsum_congr fun i => (volFun_val_eq_volume_image hU _ (hf i)).symm
  ext A hA
  rw [vol, dif_pos hadd, Measure.ofMeasurable_apply _ hA,
    Measure.comap_apply _ Subtype.val_injective (fun s hs => hU.measurableSet.subtype_image hs) _ hA]
  exact volFun_val_eq_volume_image hU A hA

/- English proof (translation)
Rewrite using `[vol_val hU]`. Conclude with `lintegral_subtype_comap hU.measurableSet g`.
-/
theorem lintegral_val (hU : IsOpen U) (g : V n → ℝ≥0∞) :
    ∫⁻ x, g x.1 ∂vol n (Subtype.val : U → V n) = ∫⁻ y in U, g y := by
  rw [vol_val hU]
  exact lintegral_subtype_comap hU.measurableSet g

/- English proof (translation)
Set `X : EtaleStein n U` to `{ z := Subtype.val isLocalHomeomorph := val_lh hU e := fun x => e x.1 smooth_e := smoothR_val he levi_e := fun x ξ => by rw [levi_val hU]; exact hel x.1 x.2 ξ isCompact_le := fun a => by`. Rewrite using `[Subtype.isCompact_iff]`. Use `hec a using 1` and compare the differences between its conclusion and the goal. Use extensionality with `y`. Simplify using `[and_comm] }`.

Take `⟨F, hFh, hFi⟩` from `ReciprocityTheory.L2DbarEstimates.hormander n U X (fun x => φ x.1) (fun x => F0 x.1) (fun x => h x.1) (smoothR_val hφ) (fun x ξ => by rw [levi_val hU]; exact hφl x.1 x.2 ξ) (smooth_val hF0) (hh.comp measurable_subtype_coe) (fun x ξ => by show ENNReal.ofReal (‖dbarDot n (Subtype.v …`. Rewrite using `[levi_val hU, dbarDot]`. Simplify using `only [db_val hU]`. Conclude with `hb x.1 x.2 ξ)`. Use `⟨ext0 F, differentiableOn_extendByZero hU hFh, ?_⟩` and prove the remaining obligations.

Establish `e1 : ∫⁻ y in U, ENNReal.ofReal (‖F0 y - ext0 F y‖ ^ 2 * Real.exp (-φ y)) = wint n (Subtype.val : U → V n) (fun x => F0 x.1 - F x) (fun x => φ x.1)`. Rewrite using `[wint, ← lintegral_val hU]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Simplify using `only [extendByZeroOnSubset_apply_coe]`. Establish `e2 : ∫⁻ y in U, h y * ENNReal.ofReal (Real.exp (-φ y)) = ∫⁻ x, h x.1 * ENNReal.ofReal (Real.exp (-φ x.1)) ∂vol n (Subtype.val : U → V n)` using `(lintegral_val hU _).symm`.

Rewrite using `[e1, e2]`. Conclude with `hFi`.
-/
theorem hormander_open (hU : IsOpen U) (e : V n → ℝ) (he : ContDiffOn ℝ ∞ e U)
    (hel : ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (e w : ℂ)) y ξ).re)
    (hec : ∀ a : ℝ, IsCompact {y | y ∈ U ∧ e y ≤ a})
    (φ : V n → ℝ) (hφ : ContDiffOn ℝ ∞ φ U)
    (hφl : ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (φ w : ℂ)) y ξ).re)
    (F0 : V n → ℂ) (hF0 : ContDiffOn ℝ ∞ F0 U) (h : V n → ℝ≥0∞) (hh : Measurable h)
    (hb : ∀ y ∈ U, ∀ ξ : Fin n → ℂ,
      ENNReal.ofReal (‖∑ j, wdb n j F0 y * (starRingEnd ℂ) (ξ j)‖ ^ 2) ≤
        h y * ENNReal.ofReal (leviV n (fun w => (φ w : ℂ)) y ξ).re) :
    ∃ F : V n → ℂ, DifferentiableOn ℂ F U ∧
      ∫⁻ y in U, ENNReal.ofReal (‖F0 y - F y‖ ^ 2 * Real.exp (-φ y)) ≤
        ∫⁻ y in U, h y * ENNReal.ofReal (Real.exp (-φ y)) := by
  let X : EtaleStein n U :=
    { z := Subtype.val
      isLocalHomeomorph := val_lh hU
      e := fun x => e x.1
      smooth_e := smoothR_val he
      levi_e := fun x ξ => by rw [levi_val hU]; exact hel x.1 x.2 ξ
      isCompact_le := fun a => by
        rw [Subtype.isCompact_iff]
        convert hec a using 1
        ext y
        simp [and_comm] }
  obtain ⟨F, hFh, hFi⟩ := ReciprocityTheory.L2DbarEstimates.hormander n U X (fun x => φ x.1) (fun x => F0 x.1)
    (fun x => h x.1) (smoothR_val hφ) (fun x ξ => by rw [levi_val hU]; exact hφl x.1 x.2 ξ)
    (smooth_val hF0) (hh.comp measurable_subtype_coe) (fun x ξ => by
      show ENNReal.ofReal (‖dbarDot n (Subtype.val : U → V n) (fun x => F0 x.1) x ξ‖ ^ 2) ≤
        h x.1 * ENNReal.ofReal (Levi n (Subtype.val : U → V n) (fun x => φ x.1) x ξ).re
      rw [levi_val hU, dbarDot]
      simp only [db_val hU]
      exact hb x.1 x.2 ξ)
  refine ⟨ext0 F, differentiableOn_extendByZero hU hFh, ?_⟩
  have e1 : ∫⁻ y in U, ENNReal.ofReal (‖F0 y - ext0 F y‖ ^ 2 * Real.exp (-φ y)) =
      wint n (Subtype.val : U → V n) (fun x => F0 x.1 - F x) (fun x => φ x.1) := by
    rw [wint, ← lintegral_val hU]
    refine lintegral_congr fun x => ?_
    simp only [extendByZeroOnSubset_apply_coe]
  have e2 : ∫⁻ y in U, h y * ENNReal.ofReal (Real.exp (-φ y)) =
      ∫⁻ x, h x.1 * ENNReal.ofReal (Real.exp (-φ x.1)) ∂vol n (Subtype.val : U → V n) :=
    (lintegral_val hU _).symm
  rw [e1, e2]
  exact hFi

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.HE

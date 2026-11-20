import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeSheets

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology

noncomputable section

variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/- English proof (translation)
Rewrite using `[← isOpen_compl_iff, isOpen_iff_mem_nhds]`. Introduce `x (hx : x ∉ S)`. Take `⟨W, hWo, hxW, r, f, hf, hSW⟩` from `hS x`. Take `⟨j, hj⟩` from `A.cover x`. Establish `hxz : ¬ ∀ i, f i x = 0`.

Introduce `hz`. Establish `hmem : x ∈ S ∩ W`. Rewrite using `[hSW]`. Conclude with `⟨hxW, hz⟩`. Conclude with `hx hmem.1`.

Use `push_neg at hxz`. Take `⟨i, hi⟩` from `hxz`. Establish `hcont : ContinuousAt (f i) x`. Establish `hxt : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W`. Use `⟨(A.chart j).map_source hj, ?_⟩` and prove the remaining obligations.

Use `show (A.chart j).symm (A.chart j x) ∈ W`. Rewrite using `[(A.chart j).left_inv hj]`. Conclude with `hxW`. Establish `h1 : ContinuousAt (f i ∘ (A.chart j).symm) (A.chart j x)` using `(hf i j _ hxt).continuousAt`. Establish `h3` using `h1.comp ((A.chart j).continuousAt hj)`.

Use `h3.congr ?_` and prove the remaining obligations. Use `filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy`. Simplify using `only [Function.comp_apply, (A.chart j).left_inv hy]`. Use `filter_upwards [hcont.eventually_ne hi, hWo.mem_nhds hxW] with y hy hyW`. Introduce `hyS`.

Establish `hmem : y ∈ S ∩ W` using `⟨hyS, hyW⟩`. Rewrite `hmem` using `[hSW]`. Conclude with `hy (hmem.2 i)`.
-/
theorem isClosed_of_isAnalyticSubset (A : FinHolAtlas e X) {S : Set X}
    (hS : A.IsAnalyticSubset S) : IsClosed S := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x (hx : x ∉ S)
  obtain ⟨W, hWo, hxW, r, f, hf, hSW⟩ := hS x
  obtain ⟨j, hj⟩ := A.cover x
  have hxz : ¬ ∀ i, f i x = 0 := by
    intro hz
    have hmem : x ∈ S ∩ W := by
      rw [hSW]
      exact ⟨hxW, hz⟩
    exact hx hmem.1
  push_neg at hxz
  obtain ⟨i, hi⟩ := hxz
  have hcont : ContinuousAt (f i) x := by
    have hxt : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W := by
      refine ⟨(A.chart j).map_source hj, ?_⟩
      show (A.chart j).symm (A.chart j x) ∈ W
      rw [(A.chart j).left_inv hj]
      exact hxW
    have h1 : ContinuousAt (f i ∘ (A.chart j).symm) (A.chart j x) := (hf i j _ hxt).continuousAt
    have h3 := h1.comp ((A.chart j).continuousAt hj)
    refine h3.congr ?_
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
    simp only [Function.comp_apply, (A.chart j).left_inv hy]
  filter_upwards [hcont.eventually_ne hi, hWo.mem_nhds hxW] with y hy hyW
  intro hyS
  have hmem : y ∈ S ∩ W := ⟨hyS, hyW⟩
  rw [hSW] at hmem
  exact hy (hmem.2 i)

/- English proof (translation)
Establish `h1 : (L.restrictScalars ℝ).det = LinearMap.det ((L : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)).restrictScalars ℝ)` using `rfl`. Rewrite using `[h1, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]`.
-/
theorem degree_det_restrictScalars (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :
    (L.restrictScalars ℝ).det =
      ‖LinearMap.det (L : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2 := by
  have h1 : (L.restrictScalars ℝ).det =
      LinearMap.det ((L : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)).restrictScalars ℝ) := rfl
  rw [h1, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]

/- English proof (translation)
Establish `hWsrc : ∀ y ∈ (B.chart j) '' W, (B.chart j).symm y ∈ W ∧ y ∈ (B.chart j).target`. Introduce and unpack `y ⟨w, hw, rfl⟩`. Use `⟨?_, (B.chart j).map_source (hWj hw)⟩` and prove the remaining obligations. Rewrite using `[(B.chart j).left_inv (hWj hw)]`. Conclude with `hw`.

Establish `hsrc : ∀ y ∈ (B.chart j) '' W, h ((B.chart j).symm y) ∈ (A.chart k).source` using `fun y hy => hVk (hbij.mapsTo (hWsrc y hy).1)`. Use `⟨?_, ?_, ?_, ?_, hsrc⟩` and prove the remaining obligations. Conclude with `((B.chart j).isOpen_image_of_subset_source hW hWj).measurableSet`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨h ((B.chart j).symm y), hbij.mapsTo (hWsrc y hy).1, rfl⟩`. Introduce and unpack `⟨v, hv, rfl⟩`. Take `⟨w, hw, rfl⟩` from `hbij.surjOn hv`. Use `⟨B.chart j w, ⟨w, hw, rfl⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only [Function.comp_apply, (B.chart j).left_inv (hWj hw)]`. Introduce and unpack `y₁ ⟨w₁, hw₁, rfl⟩ y₂ ⟨w₂, hw₂, rfl⟩ heq`. Simplify using `only [Function.comp_apply, (B.chart j).left_inv (hWj hw₁), (B.chart j).left_inv (hWj hw₂)] at heq`. Establish `hww` using `hbij.injOn hw₁ hw₂ ((A.chart k).injOn (hVk (hbij.mapsTo hw₁)) (hVk (hbij.mapsTo hw₂)) heq)`. Rewrite using `[hww]`.

Introduce `y hy`. Establish `ha : AnalyticAt ℂ (A.chart k ∘ h ∘ (B.chart j).symm) y` using `hh.2 j k y ⟨(hWsrc y hy).2, hsrc y hy⟩`. Conclude with `(ha.differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt`.
-/
theorem degree_sheet_chart_data {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X}
    (hh : HoloMap B A h) (j : Fin B.n) (k : Fin A.n) {W : Set Y} {V : Set X} (hW : IsOpen W)
    (hWj : W ⊆ (B.chart j).source) (hVk : V ⊆ (A.chart k).source) (hbij : Set.BijOn h W V) :
    MeasurableSet ((B.chart j) '' W) ∧
    (A.chart k ∘ h ∘ (B.chart j).symm) '' ((B.chart j) '' W) = (A.chart k) '' V ∧
    Set.InjOn (A.chart k ∘ h ∘ (B.chart j).symm) ((B.chart j) '' W) ∧
    (∀ y ∈ (B.chart j) '' W, HasFDerivWithinAt (A.chart k ∘ h ∘ (B.chart j).symm)
      ((fderiv ℂ (A.chart k ∘ h ∘ (B.chart j).symm) y).restrictScalars ℝ) ((B.chart j) '' W) y) ∧
    (∀ y ∈ (B.chart j) '' W, h ((B.chart j).symm y) ∈ (A.chart k).source) := by
  have hWsrc : ∀ y ∈ (B.chart j) '' W, (B.chart j).symm y ∈ W ∧ y ∈ (B.chart j).target := by
    rintro y ⟨w, hw, rfl⟩
    refine ⟨?_, (B.chart j).map_source (hWj hw)⟩
    rw [(B.chart j).left_inv (hWj hw)]
    exact hw
  have hsrc : ∀ y ∈ (B.chart j) '' W, h ((B.chart j).symm y) ∈ (A.chart k).source :=
    fun y hy => hVk (hbij.mapsTo (hWsrc y hy).1)
  refine ⟨?_, ?_, ?_, ?_, hsrc⟩
  · exact ((B.chart j).isOpen_image_of_subset_source hW hWj).measurableSet
  · ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨h ((B.chart j).symm y), hbij.mapsTo (hWsrc y hy).1, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨w, hw, rfl⟩ := hbij.surjOn hv
      refine ⟨B.chart j w, ⟨w, hw, rfl⟩, ?_⟩
      simp only [Function.comp_apply, (B.chart j).left_inv (hWj hw)]
  · rintro y₁ ⟨w₁, hw₁, rfl⟩ y₂ ⟨w₂, hw₂, rfl⟩ heq
    simp only [Function.comp_apply, (B.chart j).left_inv (hWj hw₁),
      (B.chart j).left_inv (hWj hw₂)] at heq
    have hww := hbij.injOn hw₁ hw₂
      ((A.chart k).injOn (hVk (hbij.mapsTo hw₁)) (hVk (hbij.mapsTo hw₂)) heq)
    rw [hww]
  · intro y hy
    have ha : AnalyticAt ℂ (A.chart k ∘ h ∘ (B.chart j).symm) y :=
      hh.2 j k y ⟨(hWsrc y hy).2, hsrc y hy⟩
    exact (ha.differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt

/- English proof (translation)
Take `⟨hU, himg, hinj, hder, hsrc⟩` from `degree_sheet_chart_data hh j k hW hWj hVk hbij`. Use `set φ := A.chart k ∘ h ∘ (B.chart j).symm with hφ`. Use `set G : (Fin e → ℂ) → ℝ := fun z => f ((A.chart k).symm z) * locDens A Φ k z with hG`. Establish `heq : Set.EqOn (fun y => f (h ((B.chart j).symm y)) * locDens B (fun i => (Φ i).pullback h hh.1) j y) (fun y => |((fderiv ℂ φ y).restrictScalars ℝ).det| • G (φ y)) ((B.chart j) '' W)`. Introduce `y hy`.

Establish `hyT : y ∈ (B.chart j).target`. Take `⟨w, hw, rfl⟩` from `hy`. Conclude with `(B.chart j).map_source (hWj hw)`. Simplify using `only [hG, hφ, smul_eq_mul, degree_det_restrictScalars, Function.comp_apply, (A.chart k).left_inv (hsrc y hy)]`. Rewrite using `[locDensPullback A B h hh Φ hΦ j k y hyT (hsrc y hy)]`.

Simplify using `only [abs_pow, abs_norm]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[integrableOn_congr_fun heq hU, ← himg, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hU hder hinj G]`. Rewrite using `[setIntegral_congr_fun hU heq, ← himg, integral_image_eq_integral_abs_det_fderiv_smul volume hU hder hinj G]`.
-/
theorem sheet_integral {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X}
    (hh : HoloMap B A h) (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (j : Fin B.n) (k : Fin A.n) {W : Set Y} {V : Set X} (hW : IsOpen W)
    (hWj : W ⊆ (B.chart j).source) (hVk : V ⊆ (A.chart k).source) (hbij : Set.BijOn h W V)
    (f : X → ℝ) :
    (IntegrableOn (fun y => f (h ((B.chart j).symm y)) *
        locDens B (fun i => (Φ i).pullback h hh.1) j y) ((B.chart j) '' W) ↔
      IntegrableOn (fun z => f ((A.chart k).symm z) * locDens A Φ k z) ((A.chart k) '' V)) ∧
    ∫ y in (B.chart j) '' W, f (h ((B.chart j).symm y)) *
        locDens B (fun i => (Φ i).pullback h hh.1) j y =
      ∫ z in (A.chart k) '' V, f ((A.chart k).symm z) * locDens A Φ k z := by
  obtain ⟨hU, himg, hinj, hder, hsrc⟩ := degree_sheet_chart_data hh j k hW hWj hVk hbij
  set φ := A.chart k ∘ h ∘ (B.chart j).symm with hφ
  set G : (Fin e → ℂ) → ℝ := fun z => f ((A.chart k).symm z) * locDens A Φ k z with hG
  have heq : Set.EqOn (fun y => f (h ((B.chart j).symm y)) *
        locDens B (fun i => (Φ i).pullback h hh.1) j y)
      (fun y => |((fderiv ℂ φ y).restrictScalars ℝ).det| • G (φ y)) ((B.chart j) '' W) := by
    intro y hy
    have hyT : y ∈ (B.chart j).target := by
      obtain ⟨w, hw, rfl⟩ := hy
      exact (B.chart j).map_source (hWj hw)
    simp only [hG, hφ, smul_eq_mul, degree_det_restrictScalars, Function.comp_apply,
      (A.chart k).left_inv (hsrc y hy)]
    rw [locDensPullback A B h hh Φ hΦ j k y hyT (hsrc y hy)]
    simp only [abs_pow, abs_norm]
    ring
  refine ⟨?_, ?_⟩
  · rw [integrableOn_congr_fun heq hU, ← himg,
      integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hU hder hinj G]
  · rw [setIntegral_congr_fun hU heq, ← himg,
      integral_image_eq_integral_abs_det_fderiv_smul volume hU hder hinj G]

/- English proof (translation)
Take `⟨hU, himg, hinj, hder, hsrc⟩` from `degree_sheet_chart_data hh j k hW hWj hVk hbij`. Use `set φ := A.chart k ∘ h ∘ (B.chart j).symm with hφ`. Rewrite using `[← himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hU hder hinj]`. Use `setLIntegral_congr_fun hU fun y hy => ?_` and prove the remaining obligations. Establish `hyT : y ∈ (B.chart j).target`.

Take `⟨w, hw, rfl⟩` from `hy`. Conclude with `(B.chart j).map_source (hWj hw)`. Simplify using `only [hφ, degree_det_restrictScalars, Function.comp_apply, (A.chart k).left_inv (hsrc y hy)]`. Rewrite using `[locDensPullback A B h hh Φ hΦ j k y hyT (hsrc y hy)]`. Simplify using `only [abs_mul, abs_pow, abs_norm]`.

Rewrite using `[ENNReal.ofReal_mul (abs_nonneg _)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sheet_lintegral {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X}
    (hh : HoloMap B A h) (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (j : Fin B.n) (k : Fin A.n) {W : Set Y} {V : Set X} (hW : IsOpen W)
    (hWj : W ⊆ (B.chart j).source) (hVk : V ⊆ (A.chart k).source) (hbij : Set.BijOn h W V)
    (f : X → ENNReal) :
    ∫⁻ y in (B.chart j) '' W, f (h ((B.chart j).symm y)) *
        ENNReal.ofReal |locDens B (fun i => (Φ i).pullback h hh.1) j y| =
      ∫⁻ z in (A.chart k) '' V, f ((A.chart k).symm z) * ENNReal.ofReal |locDens A Φ k z| := by
  obtain ⟨hU, himg, hinj, hder, hsrc⟩ := degree_sheet_chart_data hh j k hW hWj hVk hbij
  set φ := A.chart k ∘ h ∘ (B.chart j).symm with hφ
  rw [← himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hU hder hinj]
  refine setLIntegral_congr_fun hU fun y hy => ?_
  have hyT : y ∈ (B.chart j).target := by
    obtain ⟨w, hw, rfl⟩ := hy
    exact (B.chart j).map_source (hWj hw)
  simp only [hφ, degree_det_restrictScalars, Function.comp_apply,
    (A.chart k).left_inv (hsrc y hy)]
  rw [locDensPullback A B h hh Φ hΦ j k y hyT (hsrc y hy)]
  simp only [abs_mul, abs_pow, abs_norm]
  rw [ENNReal.ofReal_mul (abs_nonneg _)]
  ring

end

end ReciprocityTheory.AnForm.M

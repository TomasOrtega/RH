import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetOnlyNull
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteMapOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCriticalImageNull
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace SheetOnlyNull

variable {n d : ℕ}

/- English proof (translation)
Rewrite using `[← isUnit_iff_ne_zero, ← LinearMap.isUnit_iff_isUnit_det, LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot]`. Both sides reduce to the same expression.
-/
theorem injective_iff_det_ne_zero (L : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) :
    Function.Injective L ↔ LinearMap.det (L : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← LinearMap.isUnit_iff_isUnit_det, LinearMap.isUnit_iff_ker_eq_bot,
    LinearMap.ker_eq_bot]
  rfl

/- English proof (translation)
Rewrite using `[Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Complex.finrank_real_complex, smul_eq_mul, mul_comm]`.
-/
theorem finrank_real_fin_complex (d : ℕ) : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Complex.finrank_real_complex, smul_eq_mul, mul_comm]

/- English proof (translation)
The claim follows from `(LinearMap.toContinuousLinearMap B.mulVecLin).differentiable.comp_differentiableOn hs`.
-/
theorem differentiableOn_mulVec {m : ℕ} (B : Matrix (Fin m) (Fin n) ℂ) {U : Set (Fin d → ℂ)}
    {s : (Fin d → ℂ) → Fin n → ℂ} (hs : DifferentiableOn ℂ s U) :
    DifferentiableOn ℂ (fun w => B *ᵥ s w) U :=
  (LinearMap.toContinuousLinearMap B.mulVecLin).differentiable.comp_differentiableOn hs

/- English proof (translation)
Introduce `w hw` and use `AnalyticAt.pi fun i => ReciprocityTheory.AnForm.Osgood.osgood d U (fun z => F z i) hU (differentiableOn_pi.1 hF i) w hw`.
-/
theorem analyticOnNhd_of_differentiableOn {m : ℕ} {U : Set (Fin d → ℂ)}
    {F : (Fin d → ℂ) → Fin m → ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    AnalyticOnNhd ℂ F U := fun w hw =>
  AnalyticAt.pi fun i => ReciprocityTheory.AnForm.Osgood.osgood d U (fun z => F z i) hU
    (differentiableOn_pi.1 hF i) w hw

/- English proof (translation)
Introduce `w hw`. Establish `hF'` using `(analyticOnNhd_of_differentiableOn hU hF).fderiv w hw`. Establish `hent : ∀ a k, AnalyticAt ℂ (fun z => ReciprocityTheory.AnForm.A.jacC F z a k) w` using `fun a k => by show AnalyticAt ℂ (fun z => fderiv ℂ F z (Pi.single k 1) a) w`. Conclude with `(((ContinuousLinearMap.proj a).comp (ContinuousLinearMap.apply ℂ (Fin d → ℂ) (Pi.single k (1 : ℂ)))).analyticAt _).comp hF'`. Simplify using `only [Matrix.det_apply']`.

Conclude with `Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => hent _ _)`.
-/
theorem analyticOnNhd_det_jacC {U : Set (Fin d → ℂ)} {F : (Fin d → ℂ) → Fin d → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    AnalyticOnNhd ℂ (fun w => (ReciprocityTheory.AnForm.A.jacC F w).det) U := by
  intro w hw
  have hF' := (analyticOnNhd_of_differentiableOn hU hF).fderiv w hw
  have hent : ∀ a k, AnalyticAt ℂ (fun z => ReciprocityTheory.AnForm.A.jacC F z a k) w := fun a k => by
    show AnalyticAt ℂ (fun z => fderiv ℂ F z (Pi.single k 1) a) w
    exact (((ContinuousLinearMap.proj a).comp
      (ContinuousLinearMap.apply ℂ (Fin d → ℂ) (Pi.single k (1 : ℂ)))).analyticAt _).comp hF'
  simp only [Matrix.det_apply']
  exact Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul
    (Finset.analyticAt_fun_prod _ fun i _ => hent _ _)

/- English proof (translation)
Distinguish the cases in `hx : ∃ s, IsSheetAt J A x s`. Take `⟨s, U, hU, hxU, hsd, hsx, hsec, V, hV, hVs⟩` from `hx`. Establish `hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z` using `by fun_prop`. Use `⟨s, U, interior V ∩ (fun z => A *ᵥ z) ⁻¹' U, hU, isOpen_interior.inter (hU.preimage hAc), hsd, ?_, fun _ => ⟨mem_interior_iff_mem_nhds.2 hV, hxU⟩⟩` and prove the remaining obligations. Introduce and unpack `x' ⟨hx'Z, hx'V, hx'U⟩`.

Establish `hx's : s (A *ᵥ x') = x'` using `(hVs x' ⟨hx'Z, interior_subset hx'V⟩ hx'U).symm`. Conclude with `⟨hx'U, U, hU, hx'U, hsd, hx's, hsec, interior V, isOpen_interior.mem_nhds hx'V, fun x'' hx'' hAx'' => hVs x'' ⟨hx''.1, interior_subset hx''.2⟩ hAx''⟩`. Conclude with `⟨fun _ => x, ∅, ∅, isOpen_empty, isOpen_empty, differentiableOn_empty, by simp, fun h => absurd h hx⟩`.
-/
theorem exists_sheet_nhds {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (x : Fin n → ℂ) :
    ∃ (s : (Fin d → ℂ) → Fin n → ℂ) (U : Set (Fin d → ℂ)) (W : Set (Fin n → ℂ)),
      IsOpen U ∧ IsOpen W ∧ DifferentiableOn ℂ s U ∧
      (∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ U ∧ IsSheetAt J A x' s) ∧
      ((∃ s, IsSheetAt J A x s) → x ∈ W) := by
  by_cases hx : ∃ s, IsSheetAt J A x s
  · obtain ⟨s, U, hU, hxU, hsd, hsx, hsec, V, hV, hVs⟩ := hx
    have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
    refine ⟨s, U, interior V ∩ (fun z => A *ᵥ z) ⁻¹' U, hU,
      isOpen_interior.inter (hU.preimage hAc), hsd, ?_, fun _ =>
        ⟨mem_interior_iff_mem_nhds.2 hV, hxU⟩⟩
    rintro x' ⟨hx'Z, hx'V, hx'U⟩
    have hx's : s (A *ᵥ x') = x' := (hVs x' ⟨hx'Z, interior_subset hx'V⟩ hx'U).symm
    exact ⟨hx'U, U, hU, hx'U, hsd, hx's, hsec, interior V, isOpen_interior.mem_nhds hx'V,
      fun x'' hx'' hAx'' => hVs x'' ⟨hx''.1, interior_subset hx''.2⟩ hAx''⟩
  · exact ⟨fun _ => x, ∅, ∅, isOpen_empty, isOpen_empty, differentiableOn_empty,
      by simp, fun h => absurd h hx⟩

/- English proof (translation)
Take `⟨U, hU, hyU, hsd, hsx, hsec, V, hV, hVs⟩` from `hs`. Use `set F : (Fin d → ℂ) → Fin d → ℂ := fun w => A' *ᵥ s w with hFdef`. Establish `hFa` using `analyticOnNhd_of_differentiableOn hU (differentiableOn_mulVec A' hsd)`. Use `set G : Set (Fin d → ℂ) := U ∩ (fun w => (ReciprocityTheory.AnForm.A.jacC F w).det) ⁻¹' {0}ᶜ with hGdef`. Establish `hG : IsOpen G` using `(analyticOnNhd_det_jacC hU (differentiableOn_mulVec A' hsd)).continuousOn |>.isOpen_inter_preimage hU isOpen_compl_singleton`.

Establish `hinj : ∀ w, (ReciprocityTheory.AnForm.A.jacC F w).det ≠ 0 → Function.Injective (fderiv ℂ F w)` using `fun w hw => (injective_iff_det_ne_zero _).2 (by rwa [← ReciprocityTheory.AnForm.A.det_jacC])`. Establish `hequiv : ∀ w ∈ G, ∃ e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ), HasStrictFDerivAt F (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w`. Introduce `w hw`. Use `⟨(LinearEquiv.ofInjectiveEndo _ (hinj w hw.2)).toContinuousLinearEquiv, ?_⟩` and prove the remaining obligations. Conclude with `(hFa w hw.1).hasStrictFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)`.

Take `⟨e, he⟩` from `hequiv _ ⟨hyU, hdet⟩`. Use `set φ := he.toOpenPartialHomeomorph F with hφdef`. Establish `hφ : ∀ w, φ w = F w` using `fun w => by rw [hφdef, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]`. Establish `hysrc : A *ᵥ x ∈ φ.source` using `he.mem_toOpenPartialHomeomorph_source`. Establish `hFx : F (A *ᵥ x) = A' *ᵥ x` using `by simp only [hFdef, hsx]`.

Establish `hsym : φ.symm (A' *ᵥ x) = A *ᵥ x` using `by rw [← hFx, ← hφ, φ.left_inv hysrc]`. Use `⟨s ∘ φ.symm, φ.target ∩ φ.symm ⁻¹' G, φ.isOpen_inter_preimage_symm hG, ⟨by rw [← hFx, ← hφ]; exact φ.map_source hysrc, by rw [Set.mem_preimage, hsym]; exact ⟨hyU, hdet⟩⟩, ?_, by simp only [Function.comp_apply, hsym, hsx], fun z hz => ⟨?_, (hsec _ hz.2.1).2⟩, ?_⟩` and prove the remaining obligations. Introduce `z ⟨hzT, hzG⟩`. Take `⟨e', he'⟩` from `hequiv _ hzG`. Establish `hsymd : HasFDerivAt φ.symm _ z` using `φ.hasFDerivAt_symm hzT (f' := e') (by`.

Establish `: (φ : (Fin d → ℂ) → Fin d → ℂ) = F` using `funext hφ`. Rewrite using `[this]`. Conclude with `he'.hasFDerivAt)`. Conclude with `((hsd.differentiableAt (hU.mem_nhds hzG.1)).comp z hsymd.differentiableAt).differentiableWithinAt`. Use `show F (φ.symm z) = z`.

Rewrite using `[← hφ, φ.right_inv hz.1]`. Use `⟨V ∩ (fun z => A *ᵥ z) ⁻¹' (φ.source ∩ U), inter_mem hV (((φ.open_source.inter hU).preimage (by fun_prop)).mem_nhds ⟨hysrc, hyU⟩), ?_⟩` and prove the remaining obligations. Introduce and unpack `x'' ⟨hx''Z, hx''V, hx''src, hx''U⟩ -`. Establish `hx'' : x'' = s (A *ᵥ x'')` using `hVs x'' ⟨hx''Z, hx''V⟩ hx''U`. Establish `hA' : A' *ᵥ x'' = φ (A *ᵥ x'')` using `by rw [hφ, hFdef]; exact congrArg _ hx''`.

Rewrite using `[Function.comp_apply, hA', φ.left_inv hx''src]`. Conclude with `hx''`.
-/
theorem exists_sheet_of_det_ne_zero {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A A' : Matrix (Fin d) (Fin n) ℂ} {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ}
    (hs : IsSheetAt J A x s)
    (hdet : (ReciprocityTheory.AnForm.A.jacC (fun w => A' *ᵥ s w) (A *ᵥ x)).det ≠ 0) :
    ∃ s', IsSheetAt J A' x s' := by
  obtain ⟨U, hU, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hs
  set F : (Fin d → ℂ) → Fin d → ℂ := fun w => A' *ᵥ s w with hFdef
  have hFa := analyticOnNhd_of_differentiableOn hU (differentiableOn_mulVec A' hsd)
  set G : Set (Fin d → ℂ) := U ∩ (fun w => (ReciprocityTheory.AnForm.A.jacC F w).det) ⁻¹' {0}ᶜ with hGdef
  have hG : IsOpen G := (analyticOnNhd_det_jacC hU (differentiableOn_mulVec A' hsd)).continuousOn
    |>.isOpen_inter_preimage hU isOpen_compl_singleton
  have hinj : ∀ w, (ReciprocityTheory.AnForm.A.jacC F w).det ≠ 0 → Function.Injective (fderiv ℂ F w) :=
    fun w hw => (injective_iff_det_ne_zero _).2 (by rwa [← ReciprocityTheory.AnForm.A.det_jacC])
  have hequiv : ∀ w ∈ G, ∃ e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ),
      HasStrictFDerivAt F (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w := by
    intro w hw
    refine ⟨(LinearEquiv.ofInjectiveEndo _ (hinj w hw.2)).toContinuousLinearEquiv, ?_⟩
    exact (hFa w hw.1).hasStrictFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  obtain ⟨e, he⟩ := hequiv _ ⟨hyU, hdet⟩
  set φ := he.toOpenPartialHomeomorph F with hφdef
  have hφ : ∀ w, φ w = F w := fun w => by rw [hφdef, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
  have hysrc : A *ᵥ x ∈ φ.source := he.mem_toOpenPartialHomeomorph_source
  have hFx : F (A *ᵥ x) = A' *ᵥ x := by simp only [hFdef, hsx]
  have hsym : φ.symm (A' *ᵥ x) = A *ᵥ x := by rw [← hFx, ← hφ, φ.left_inv hysrc]
  refine ⟨s ∘ φ.symm, φ.target ∩ φ.symm ⁻¹' G, φ.isOpen_inter_preimage_symm hG,
    ⟨by rw [← hFx, ← hφ]; exact φ.map_source hysrc, by rw [Set.mem_preimage, hsym]; exact ⟨hyU, hdet⟩⟩,
    ?_, by simp only [Function.comp_apply, hsym, hsx], fun z hz => ⟨?_, (hsec _ hz.2.1).2⟩, ?_⟩
  · intro z ⟨hzT, hzG⟩
    obtain ⟨e', he'⟩ := hequiv _ hzG
    have hsymd : HasFDerivAt φ.symm _ z :=
      φ.hasFDerivAt_symm hzT (f' := e') (by
        have : (φ : (Fin d → ℂ) → Fin d → ℂ) = F := funext hφ
        rw [this]; exact he'.hasFDerivAt)
    exact ((hsd.differentiableAt (hU.mem_nhds hzG.1)).comp z
      hsymd.differentiableAt).differentiableWithinAt
  · show F (φ.symm z) = z
    rw [← hφ, φ.right_inv hz.1]
  · refine ⟨V ∩ (fun z => A *ᵥ z) ⁻¹' (φ.source ∩ U), inter_mem hV
      (((φ.open_source.inter hU).preimage (by fun_prop)).mem_nhds ⟨hysrc, hyU⟩), ?_⟩
    rintro x'' ⟨hx''Z, hx''V, hx''src, hx''U⟩ -
    have hx'' : x'' = s (A *ᵥ x'') := hVs x'' ⟨hx''Z, hx''V⟩ hx''U
    have hA' : A' *ᵥ x'' = φ (A *ᵥ x'') := by rw [hφ, hFdef]; exact congrArg _ hx''
    rw [Function.comp_apply, hA', φ.left_inv hx''src]
    exact hx''

/- English proof (translation)
Take `⟨U, hU, hyU, hsd, hsx, hsec, V, hV, hVs⟩` from `hs`. Use `set F : (Fin d → ℂ) → Fin d → ℂ := fun w => A' *ᵥ s w with hFdef`. Assume the negation of the conclusion as `hall`. Use `push Not at hall`. Establish `hcrit : F '' (W₀ ∩ U) ⊆ F '' {w | w ∈ U ∧ ¬ Function.Injective (fderiv ℂ F w)}` using `Set.image_mono fun w hw => ⟨hw.2, fun hinj => (injective_iff_det_ne_zero _).1 hinj (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hall w hw.1)⟩`.

Establish `hnull` using `measure_mono_null hcrit (h₂ d d U F hU (differentiableOn_mulVec A' hsd))`. Establish `hxZ : x ∈ zeroSet J` using `hsx ▸ (hsec _ hyU).2`. Establish `hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z` using `by fun_prop`. Establish `hnhds` using `h₁ n d J (linPoly A') hJ hA'.injective hA'.finite x hxZ (V ∩ (fun z => A *ᵥ z) ⁻¹' (W₀ ∩ U)) (inter_mem hV (((hW₀.inter hU).preimage hAc).mem_nhds ⟨hxW₀, hyU⟩))`. Establish `hev : ∀ z : Fin n → ℂ, (fun i => eval z (linPoly A' i)) = A' *ᵥ z` using `fun z => by`.

Use extensionality with `i`. Simplify using `[linPoly, Matrix.mulVec, dotProduct]`. Simplify using `only [hev] at hnhds`. Establish `hsub : (fun z => A' *ᵥ z) '' (IndefiniteRowSideFullHecke.ComplexSets.zeroLocus J ∩ (V ∩ (fun z => A *ᵥ z) ⁻¹' (W₀ ∩ U))) ⊆ F '' (W₀ ∩ U)`. Introduce and unpack `_ ⟨z, ⟨hzZ, hzV, hzW⟩, rfl⟩`.

Use `⟨A *ᵥ z, hzW, ?_⟩` and prove the remaining obligations. Simplify using `only [hFdef]`. Rewrite using `[← hVs z ⟨hzZ, hzV⟩ hzW.2]`. Establish `hpos` using `Measure.measure_pos_of_mem_nhds (μ := μH[(Module.finrank ℝ (Fin d → ℂ) : ℝ)]) (Filter.mem_of_superset hnhds hsub)`. Rewrite `hpos` using `[finrank_real_fin_complex]`.

Conclude with `hpos.ne' hnull`.
-/
theorem exists_det_ne_zero (h₁ : IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A A' : Matrix (Fin d) (Fin n) ℂ} (hJ : J.IsPrime) (hA' : IsFiniteProjection J A')
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s)
    {W₀ : Set (Fin d → ℂ)} (hW₀ : IsOpen W₀) (hxW₀ : A *ᵥ x ∈ W₀) :
    ∃ w ∈ W₀, (ReciprocityTheory.AnForm.A.jacC (fun w => A' *ᵥ s w) w).det ≠ 0 := by
  obtain ⟨U, hU, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hs
  set F : (Fin d → ℂ) → Fin d → ℂ := fun w => A' *ᵥ s w with hFdef
  by_contra hall
  push Not at hall
  have hcrit : F '' (W₀ ∩ U) ⊆ F '' {w | w ∈ U ∧ ¬ Function.Injective (fderiv ℂ F w)} :=
    Set.image_mono fun w hw => ⟨hw.2, fun hinj => (injective_iff_det_ne_zero _).1 hinj
      (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hall w hw.1)⟩
  have hnull := measure_mono_null hcrit (h₂ d d U F hU (differentiableOn_mulVec A' hsd))
  have hxZ : x ∈ zeroSet J := hsx ▸ (hsec _ hyU).2
  have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
  have hnhds := h₁ n d J (linPoly A') hJ hA'.injective hA'.finite x hxZ
    (V ∩ (fun z => A *ᵥ z) ⁻¹' (W₀ ∩ U))
    (inter_mem hV (((hW₀.inter hU).preimage hAc).mem_nhds ⟨hxW₀, hyU⟩))
  have hev : ∀ z : Fin n → ℂ, (fun i => eval z (linPoly A' i)) = A' *ᵥ z := fun z => by
    ext i
    simp [linPoly, Matrix.mulVec, dotProduct]
  simp only [hev] at hnhds
  have hsub : (fun z => A' *ᵥ z) '' (IndefiniteRowSideFullHecke.ComplexSets.zeroLocus J ∩
      (V ∩ (fun z => A *ᵥ z) ⁻¹' (W₀ ∩ U))) ⊆ F '' (W₀ ∩ U) := by
    rintro _ ⟨z, ⟨hzZ, hzV, hzW⟩, rfl⟩
    refine ⟨A *ᵥ z, hzW, ?_⟩
    simp only [hFdef]
    rw [← hVs z ⟨hzZ, hzV⟩ hzW.2]
  have hpos := Measure.measure_pos_of_mem_nhds (μ := μH[(Module.finrank ℝ (Fin d → ℂ) : ℝ)])
    (Filter.mem_of_superset hnhds hsub)
  rw [finrank_real_fin_complex] at hpos
  exact hpos.ne' hnull

end SheetOnlyNull

/- English proof (translation)
Introduce `n d J A A' hJ _ _ hA'`. Use `set B := {x | x ∈ zeroSet J ∧ (∃ s, IsSheetAt J A x s) ∧ ¬ ∃ s', IsSheetAt J A' x s'} with hBdef`. Use `choose σ U W hU hW hσd hWsh hxW using fun x : Fin n → ℂ => SheetOnlyNull.exists_sheet_nhds (J := J) (A := A) x`. Take `⟨T, hTc, hTU⟩` from `TopologicalSpace.isOpen_iUnion_countable W hW`. Establish `hpiece : ∀ i, volume ((fun x => A *ᵥ x) '' (B ∩ W i)) = 0`.

Introduce `i`. Apply `ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, ⟨hxB, hxWi⟩, rfl⟩`. Take `⟨hAx, hsh⟩` from `hWsh i x ⟨hxB.1, hxWi⟩`. Take `⟨r, hr, hball⟩` from `Metric.isOpen_iff.mp (hU i) _ hAx`.

Use `⟨Metric.ball (A *ᵥ x) r, Metric.isOpen_ball, Metric.mem_ball_self hr, (convex_ball _ r).isPreconnected, fun w => (ReciprocityTheory.AnForm.A.jacC (fun v => A' *ᵥ σ i v) w).det, (SheetOnlyNull.analyticOnNhd_det_jacC (hU i) (SheetOnlyNull.differentiableOn_mulVec A' (hσd i))).mono h …` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨x'', ⟨hx''B, hx''W⟩, rfl⟩, -⟩`. Assume the negation of the conclusion as `hne`. Conclude with `hx''B.2.2 (SheetOnlyNull.exists_sheet_of_det_ne_zero (hWsh i x'' ⟨hx''B.1, hx''W⟩).2 hne)`. Use `measure_mono_null ?_ ((measure_biUnion_null_iff hTc).2 fun i _ => hpiece i)` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, hxB, rfl⟩`. Establish `hx : x ∈ ⋃ i ∈ T, W i` using `hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x hxB.2.1⟩`. Take `⟨i, hiT, hxi⟩` from `Set.mem_iUnion₂.1 hx`. Conclude with `Set.mem_biUnion hiT ⟨x, ⟨hxB, hxi⟩, rfl⟩`.
-/
theorem SheetOnlyNull.proof (h₁ : IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement) : SheetOnlyNull.Statement := by
  intro n d J A A' hJ _ _ hA'
  set B := {x | x ∈ zeroSet J ∧ (∃ s, IsSheetAt J A x s) ∧ ¬ ∃ s', IsSheetAt J A' x s'} with hBdef
  choose σ U W hU hW hσd hWsh hxW using
    fun x : Fin n → ℂ => SheetOnlyNull.exists_sheet_nhds (J := J) (A := A) x
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  have hpiece : ∀ i, volume ((fun x => A *ᵥ x) '' (B ∩ W i)) = 0 := by
    intro i
    apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
    rintro _ ⟨x, ⟨hxB, hxWi⟩, rfl⟩
    obtain ⟨hAx, hsh⟩ := hWsh i x ⟨hxB.1, hxWi⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hU i) _ hAx
    refine ⟨Metric.ball (A *ᵥ x) r, Metric.isOpen_ball, Metric.mem_ball_self hr,
      (convex_ball _ r).isPreconnected,
      fun w => (ReciprocityTheory.AnForm.A.jacC (fun v => A' *ᵥ σ i v) w).det,
      (SheetOnlyNull.analyticOnNhd_det_jacC (hU i)
        (SheetOnlyNull.differentiableOn_mulVec A' (hσd i))).mono hball,
      SheetOnlyNull.exists_det_ne_zero h₁ h₂ hJ hA' hsh Metric.isOpen_ball (Metric.mem_ball_self hr),
      ?_⟩
    rintro _ ⟨⟨x'', ⟨hx''B, hx''W⟩, rfl⟩, -⟩
    by_contra hne
    exact hx''B.2.2 (SheetOnlyNull.exists_sheet_of_det_ne_zero (hWsh i x'' ⟨hx''B.1, hx''W⟩).2 hne)
  refine measure_mono_null ?_ ((measure_biUnion_null_iff hTc).2 fun i _ => hpiece i)
  rintro _ ⟨x, hxB, rfl⟩
  have hx : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x hxB.2.1⟩
  obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 hx
  exact Set.mem_biUnion hiT ⟨x, ⟨hxB, hxi⟩, rfl⟩

end

end GroundTheory.Heights₂.Heights

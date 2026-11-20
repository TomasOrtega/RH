import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StRatSheetCover
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StRatFibreAvoid
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetOnlyNull
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantSheetCover
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalOpenMapping
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelOpenMapping
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

namespace RatSheetCover

variable {n d : ℕ}

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a => simp only [eval_C]`. Conclude with `differentiable_const a`. Consider the case `add p q hp hq => simp only [map_add]`. Conclude with `hp.add hq`.

Consider the case `mul_X p i hp => simp only [map_mul, eval_X]`. Conclude with `hp.mul (differentiable_apply i)`.
-/
theorem differentiable_eval_poly (g : MvPolynomial (Fin n) ℂ) : Differentiable ℂ (fun x => eval x g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp only [eval_C]; exact differentiable_const a
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, eval_X]; exact hp.mul (differentiable_apply i)

/- English proof (translation)
Use `show DifferentiableAt ℂ (fun z => fun r => eval z (p r) / eval z q) x`. Use `differentiableAt_pi.2 fun r => ?_` and prove the remaining obligations. Use `show DifferentiableAt ℂ (fun z => eval z (p r) / eval z q) x`. Simplify using `only [div_eq_mul_inv]`. Conclude with `(differentiable_eval_poly (p r) x).mul ((differentiable_eval_poly q x).inv hx)`.
-/
theorem differentiableAt_ratMap (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
    {x : Fin n → ℂ} (hx : eval x q ≠ 0) : DifferentiableAt ℂ (RatChart.ratMap p q) x := by
  show DifferentiableAt ℂ (fun z => fun r => eval z (p r) / eval z q) x
  refine differentiableAt_pi.2 fun r => ?_
  show DifferentiableAt ℂ (fun z => eval z (p r) / eval z q) x
  simp only [div_eq_mul_inv]
  exact (differentiable_eval_poly (p r) x).mul ((differentiable_eval_poly q x).inv hx)

/- English proof (translation)
Rewrite `h` using `[← SheetOnlyNull.finrank_real_fin_complex]`. Conclude with `Measure.absolutelyContinuous_isAddHaarMeasure _ _ h`.
-/
theorem volume_eq_zero_of_hausdorff {S : Set (Fin d → ℂ)} (h : μH[((2 * d : ℕ) : ℝ)] S = 0) :
    volume S = 0 := by
  rw [← SheetOnlyNull.finrank_real_fin_complex] at h
  exact Measure.absolutelyContinuous_isAddHaarMeasure _ _ h

/- English proof (translation)
Take `⟨U, hU, hyU, hsd, hsx, hsec, V, hV, hVs⟩` from `hσ`. Use `set F : (Fin d → ℂ) → Fin d → ℂ := fun t => RatChart.ratMap p q (σ t) with hFdef`. Use `set W : Set (Fin d → ℂ) := U ∩ σ ⁻¹' {z | eval z q ≠ 0} with hWdef`. Establish `hW : IsOpen W` using `hsd.continuousOn.isOpen_inter_preimage hU (isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const)`. Establish `hFd : DifferentiableOn ℂ F W` using `fun t ht => ((differentiableAt_ratMap p q ht.2).comp t (hsd.differentiableAt (hU.mem_nhds ht.1))).differentiableWithinAt`.

Establish `hFa` using `SheetOnlyNull.analyticOnNhd_of_differentiableOn hW hFd`. Establish `hxW : A *ᵥ x ∈ W` using `⟨hyU, by simp only [Set.mem_preimage, Set.mem_ofPred_eq, hsx]; exact hq⟩`. Use `set G : Set (Fin d → ℂ) := W ∩ (fun w => (ReciprocityTheory.AnForm.A.jacC F w).det) ⁻¹' {0}ᶜ with hGdef`. Establish `hG : IsOpen G` using `(SheetOnlyNull.analyticOnNhd_det_jacC hW hFd).continuousOn |>.isOpen_inter_preimage hW isOpen_compl_singleton`. Establish `hdet : (ReciprocityTheory.AnForm.A.jacC F (A *ᵥ x)).det ≠ 0`.

Rewrite using `[ReciprocityTheory.AnForm.A.det_jacC]`. Conclude with `(SheetOnlyNull.injective_iff_det_ne_zero _).1 hinj`. Establish `hinj' : ∀ w, (ReciprocityTheory.AnForm.A.jacC F w).det ≠ 0 → Function.Injective (fderiv ℂ F w)` using `fun w hw => (SheetOnlyNull.injective_iff_det_ne_zero _).2 (by rwa [← ReciprocityTheory.AnForm.A.det_jacC])`. Establish `hequiv : ∀ w ∈ G, ∃ e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ), HasStrictFDerivAt F (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w`. Introduce `w hw`.

Use `⟨(LinearEquiv.ofInjectiveEndo _ (hinj' w hw.2)).toContinuousLinearEquiv, ?_⟩` and prove the remaining obligations. Conclude with `(hFa w hw.1).hasStrictFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)`. Take `⟨e, he⟩` from `hequiv _ ⟨hxW, hdet⟩`. Use `set φ := he.toOpenPartialHomeomorph F with hφdef`. Establish `hφ : ∀ w, φ w = F w` using `fun w => by rw [hφdef, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]`.

Establish `hysrc : A *ᵥ x ∈ φ.source` using `he.mem_toOpenPartialHomeomorph_source`. Establish `hFx : F (A *ᵥ x) = RatChart.ratMap p q x` using `by simp only [hFdef, hsx]`. Establish `hsym : φ.symm (RatChart.ratMap p q x) = A *ᵥ x` using `by rw [← hFx, ← hφ, φ.left_inv hysrc]`. Use `⟨σ ∘ φ.symm, φ.target ∩ φ.symm ⁻¹' G, φ.isOpen_inter_preimage_symm hG, ⟨by rw [← hFx, ← hφ]; exact φ.map_source hysrc, by rw [Set.mem_preimage, hsym]; exact ⟨hxW, hdet⟩⟩, ?_, by simp only [Function.comp_apply, hsym, hsx], fun z hz => ⟨(hsec _ hz.2.1.1).2, hz.2.1.2, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `z ⟨hzT, hzG⟩`.

Take `⟨e', he'⟩` from `hequiv _ hzG`. Establish `hsymd : HasFDerivAt φ.symm _ z` using `φ.hasFDerivAt_symm hzT (f' := e') (by`. Establish `: (φ : (Fin d → ℂ) → Fin d → ℂ) = F` using `funext hφ`. Rewrite using `[this]`. Conclude with `he'.hasFDerivAt)`.

Conclude with `((hsd.differentiableAt (hU.mem_nhds hzG.1.1)).comp z hsymd.differentiableAt).differentiableWithinAt`. Use `show F (φ.symm z) = z`. Rewrite using `[← hφ, φ.right_inv hz.1]`. Use `⟨V ∩ (fun z => A *ᵥ z) ⁻¹' (φ.source ∩ U), inter_mem hV (((φ.open_source.inter hU).preimage (by fun_prop)).mem_nhds ⟨hysrc, hyU⟩), ?_⟩` and prove the remaining obligations. Introduce and unpack `x'' ⟨hx''Z, hx''V, hx''src, hx''U⟩ - -`.

Establish `hx'' : x'' = σ (A *ᵥ x'')` using `hVs x'' ⟨hx''Z, hx''V⟩ hx''U`. Establish `hR : RatChart.ratMap p q x'' = φ (A *ᵥ x'')`. Rewrite using `[hφ, hFdef]`. Conclude with `congrArg _ hx''`. Rewrite using `[Function.comp_apply, hR, φ.left_inv hx''src]`.

Conclude with `hx''`.
-/
theorem exists_ratSheet {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {p : Fin d → MvPolynomial (Fin n) ℂ} {q : MvPolynomial (Fin n) ℂ} {x : Fin n → ℂ}
    {σ : (Fin d → ℂ) → Fin n → ℂ} (hσ : IsSheetAt J A x σ) (hq : eval x q ≠ 0)
    (hinj : Function.Injective (fderiv ℂ (fun t => RatChart.ratMap p q (σ t)) (A *ᵥ x))) :
    ∃ s, RatChart.IsRatSheetAt J p q x s := by
  obtain ⟨U, hU, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hσ
  set F : (Fin d → ℂ) → Fin d → ℂ := fun t => RatChart.ratMap p q (σ t) with hFdef
  set W : Set (Fin d → ℂ) := U ∩ σ ⁻¹' {z | eval z q ≠ 0} with hWdef
  have hW : IsOpen W := hsd.continuousOn.isOpen_inter_preimage hU
    (isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const)
  have hFd : DifferentiableOn ℂ F W := fun t ht =>
    ((differentiableAt_ratMap p q ht.2).comp t
      (hsd.differentiableAt (hU.mem_nhds ht.1))).differentiableWithinAt
  have hFa := SheetOnlyNull.analyticOnNhd_of_differentiableOn hW hFd
  have hxW : A *ᵥ x ∈ W := ⟨hyU, by simp only [Set.mem_preimage, Set.mem_ofPred_eq, hsx]; exact hq⟩
  set G : Set (Fin d → ℂ) := W ∩ (fun w => (ReciprocityTheory.AnForm.A.jacC F w).det) ⁻¹' {0}ᶜ with hGdef
  have hG : IsOpen G := (SheetOnlyNull.analyticOnNhd_det_jacC hW hFd).continuousOn
    |>.isOpen_inter_preimage hW isOpen_compl_singleton
  have hdet : (ReciprocityTheory.AnForm.A.jacC F (A *ᵥ x)).det ≠ 0 := by
    rw [ReciprocityTheory.AnForm.A.det_jacC]
    exact (SheetOnlyNull.injective_iff_det_ne_zero _).1 hinj
  have hinj' : ∀ w, (ReciprocityTheory.AnForm.A.jacC F w).det ≠ 0 → Function.Injective (fderiv ℂ F w) :=
    fun w hw => (SheetOnlyNull.injective_iff_det_ne_zero _).2 (by rwa [← ReciprocityTheory.AnForm.A.det_jacC])
  have hequiv : ∀ w ∈ G, ∃ e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ),
      HasStrictFDerivAt F (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w := by
    intro w hw
    refine ⟨(LinearEquiv.ofInjectiveEndo _ (hinj' w hw.2)).toContinuousLinearEquiv, ?_⟩
    exact (hFa w hw.1).hasStrictFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  obtain ⟨e, he⟩ := hequiv _ ⟨hxW, hdet⟩
  set φ := he.toOpenPartialHomeomorph F with hφdef
  have hφ : ∀ w, φ w = F w := fun w => by rw [hφdef, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
  have hysrc : A *ᵥ x ∈ φ.source := he.mem_toOpenPartialHomeomorph_source
  have hFx : F (A *ᵥ x) = RatChart.ratMap p q x := by simp only [hFdef, hsx]
  have hsym : φ.symm (RatChart.ratMap p q x) = A *ᵥ x := by rw [← hFx, ← hφ, φ.left_inv hysrc]
  refine ⟨σ ∘ φ.symm, φ.target ∩ φ.symm ⁻¹' G, φ.isOpen_inter_preimage_symm hG,
    ⟨by rw [← hFx, ← hφ]; exact φ.map_source hysrc, by rw [Set.mem_preimage, hsym]; exact ⟨hxW, hdet⟩⟩,
    ?_, by simp only [Function.comp_apply, hsym, hsx], fun z hz => ⟨(hsec _ hz.2.1.1).2, hz.2.1.2, ?_⟩, ?_⟩
  · intro z ⟨hzT, hzG⟩
    obtain ⟨e', he'⟩ := hequiv _ hzG
    have hsymd : HasFDerivAt φ.symm _ z :=
      φ.hasFDerivAt_symm hzT (f' := e') (by
        have : (φ : (Fin d → ℂ) → Fin d → ℂ) = F := funext hφ
        rw [this]; exact he'.hasFDerivAt)
    exact ((hsd.differentiableAt (hU.mem_nhds hzG.1.1)).comp z
      hsymd.differentiableAt).differentiableWithinAt
  · show F (φ.symm z) = z
    rw [← hφ, φ.right_inv hz.1]
  · refine ⟨V ∩ (fun z => A *ᵥ z) ⁻¹' (φ.source ∩ U), inter_mem hV
      (((φ.open_source.inter hU).preimage (by fun_prop)).mem_nhds ⟨hysrc, hyU⟩), ?_⟩
    rintro x'' ⟨hx''Z, hx''V, hx''src, hx''U⟩ - -
    have hx'' : x'' = σ (A *ᵥ x'') := hVs x'' ⟨hx''Z, hx''V⟩ hx''U
    have hR : RatChart.ratMap p q x'' = φ (A *ᵥ x'') := by
      rw [hφ, hFdef]; exact congrArg _ hx''
    rw [Function.comp_apply, hR, φ.left_inv hx''src]
    exact hx''

end RatSheetCover

/- English proof (translation)
Introduce `n d J p q hJ hdim`. Take `⟨A, hA⟩` from `IndefiniteRowSideFullHecke.ComplexSets.exists_isFiniteProjection J hJ hdim`. Take `⟨P, U, D, N, s, hP, hUD, -, hcov, -, hfib⟩` from `DiscriminantSheetCover.proof ComplexSets.DiscriminantCover.full n d J A hJ hdim hA`. Establish `hf : pullback A P ∉ J` using `fun h => hP (hA.injective (a₁ := P) (a₂ := 0) (by`. Simplify using `only [map_zero, projHom, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 h))`. Establish `hav` using `h₁ n d J p q (pullback A P) hJ hdim hf`. Use `set Crit : Set (Fin d → ℂ) := ⋃ k, ⋃ j : Fin (N k), (fun t => RatChart.ratMap p q (s k j t)) '' {t | t ∈ U k ∩ s k j ⁻¹' {z | eval z q ≠ 0} ∧ ¬ Function.Injective (fderiv ℂ (fun t => RatChart.ratMap p q (s k j t)) t)} with hCritdef`. Establish `hCrit : volume Crit = 0`. Use `measure_iUnion_null fun k => measure_iUnion_null fun j => ?_` and prove the remaining obligations.

Establish `hW : IsOpen (U k ∩ s k j ⁻¹' {z | eval z q ≠ 0})` using `((hUD k).2.2.2 j).continuousOn.isOpen_inter_preimage (hUD k).1 (isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const)`. Establish `hFd : DifferentiableOn ℂ (fun t => RatChart.ratMap p q (s k j t)) (U k ∩ s k j ⁻¹' {z | eval z q ≠ 0})` using `fun t ht => ((RatSheetCover.differentiableAt_ratMap p q ht.2).comp t (((hUD k).2.2.2 j).differentiableAt ((hUD k).1.mem_nhds ht.1))).differentiableWithinAt`. Conclude with `RatSheetCover.volume_eq_zero_of_hausdorff (IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.full d d _ _ hW hFd)`. Use `filter_upwards [hav, compl_mem_ae_iff.2 hCrit] with y hy hyC x hx`. Take `⟨hxZ, hxq, hxy⟩` from `hx`.

Establish `hPx : eval (A *ᵥ x) P ≠ 0`. Rewrite using `[← IndefiniteRowSideFullHecke.ComplexSets.eval_pullback_eq]`. Conclude with `hy x ⟨hxZ, hxq, hxy⟩`. Establish `hmem : A *ᵥ x ∈ ⋃ k, D k`. Assume the negation of the conclusion as `h`.

Conclude with `hPx (hcov h)`. Take `⟨k, hk⟩` from `Set.mem_iUnion.1 hmem`. Establish `hAU : A *ᵥ x ∈ U k` using `(hUD k).2.2.1 hk`. Take `⟨hrange, -, hsh⟩` from `hfib k _ hAU`. Establish `hxf : x ∈ fibre J A (A *ᵥ x)` using `⟨hxZ, rfl⟩`.

Rewrite `hxf` using `[hrange]`. Take `⟨j, hj⟩` from `hxf`. Establish `hσ : IsSheetAt J A x (s k j)`. Use `hsh j` as an intermediate fact. Simplify using `only at hj`.

Rewrite `this` using `[hj]`. Then use the resulting hypothesis. Use `RatSheetCover.exists_ratSheet hσ hxq ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hni`. Use `hyC (Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨j, A *ᵥ x, ⟨⟨hAU, ?_⟩, hni⟩, ?_⟩⟩)` and prove the remaining obligations. Simplify using `only [Set.mem_preimage, Set.mem_ofPred_eq, hj]`.

Conclude with `hxq`. Simplify using `only [hj, hxy]`.
-/
theorem RatSheetCover.proof (h₁ : RatFibreAvoid.Statement) : RatSheetCover.Statement := by
  intro n d J p q hJ hdim
  obtain ⟨A, hA⟩ := IndefiniteRowSideFullHecke.ComplexSets.exists_isFiniteProjection J hJ hdim
  obtain ⟨P, U, D, N, s, hP, hUD, -, hcov, -, hfib⟩ :=
    DiscriminantSheetCover.proof ComplexSets.DiscriminantCover.full n d J A hJ hdim hA
  have hf : pullback A P ∉ J := fun h => hP (hA.injective (a₁ := P) (a₂ := 0) (by
    simp only [map_zero, projHom, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.2 h))
  have hav := h₁ n d J p q (pullback A P) hJ hdim hf
  set Crit : Set (Fin d → ℂ) := ⋃ k, ⋃ j : Fin (N k),
    (fun t => RatChart.ratMap p q (s k j t)) ''
      {t | t ∈ U k ∩ s k j ⁻¹' {z | eval z q ≠ 0} ∧
        ¬ Function.Injective (fderiv ℂ (fun t => RatChart.ratMap p q (s k j t)) t)} with hCritdef
  have hCrit : volume Crit = 0 := by
    refine measure_iUnion_null fun k => measure_iUnion_null fun j => ?_
    have hW : IsOpen (U k ∩ s k j ⁻¹' {z | eval z q ≠ 0}) :=
      ((hUD k).2.2.2 j).continuousOn.isOpen_inter_preimage (hUD k).1
        (isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const)
    have hFd : DifferentiableOn ℂ (fun t => RatChart.ratMap p q (s k j t))
        (U k ∩ s k j ⁻¹' {z | eval z q ≠ 0}) := fun t ht =>
      ((RatSheetCover.differentiableAt_ratMap p q ht.2).comp t
        (((hUD k).2.2.2 j).differentiableAt ((hUD k).1.mem_nhds ht.1))).differentiableWithinAt
    exact RatSheetCover.volume_eq_zero_of_hausdorff
      (IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.full d d _ _ hW hFd)
  filter_upwards [hav, compl_mem_ae_iff.2 hCrit] with y hy hyC x hx
  obtain ⟨hxZ, hxq, hxy⟩ := hx
  have hPx : eval (A *ᵥ x) P ≠ 0 := by
    rw [← IndefiniteRowSideFullHecke.ComplexSets.eval_pullback_eq]; exact hy x ⟨hxZ, hxq, hxy⟩
  have hmem : A *ᵥ x ∈ ⋃ k, D k := by
    by_contra h
    exact hPx (hcov h)
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hmem
  have hAU : A *ᵥ x ∈ U k := (hUD k).2.2.1 hk
  obtain ⟨hrange, -, hsh⟩ := hfib k _ hAU
  have hxf : x ∈ fibre J A (A *ᵥ x) := ⟨hxZ, rfl⟩
  rw [hrange] at hxf
  obtain ⟨j, hj⟩ := hxf
  have hσ : IsSheetAt J A x (s k j) := by
    have := hsh j
    simp only at hj
    rwa [hj] at this
  refine RatSheetCover.exists_ratSheet hσ hxq ?_
  by_contra hni
  refine hyC (Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨j, A *ᵥ x, ⟨⟨hAU, ?_⟩, hni⟩, ?_⟩⟩)
  · simp only [Set.mem_preimage, Set.mem_ofPred_eq, hj]; exact hxq
  · simp only [hj, hxy]

end GroundTheory.Heights₂.Heights

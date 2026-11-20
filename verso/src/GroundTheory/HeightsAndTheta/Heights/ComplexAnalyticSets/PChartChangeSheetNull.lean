import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartChangeSheetNull
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetOnlyNull
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantSheetCover
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBadSetSmaller
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace ChartChangeSheetNull

variable {n d : ℕ}

/- English proof (translation)
Simplify using `[linForm, linEval]`.
-/
theorem eval_linForm (u x : Fin n → ℂ) : eval x (linForm u) = linEval u x := by
  simp [linForm, linEval]

/- English proof (translation)
Unfold `linEval`. Use `fun_prop`.
-/
theorem continuous_linEval (u : Fin n → ℂ) : Continuous (linEval u) := by
  unfold linEval
  fun_prop

/- English proof (translation)
Establish `hv0 : Ideal.Quotient.mk J (linForm u) ≠ 0`. Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hu`. Establish `hex : ∃ k, ∃ p : Polynomial (MvPolynomial (Fin d) ℂ), p.Monic ∧ p.natDegree = k ∧ p.eval₂ (projHom J A).toRingHom (Ideal.Quotient.mk J (linForm u)) = 0`. Take `⟨p, hpm, hp⟩` from `hA.finite.to_isIntegral (Ideal.Quotient.mk J (linForm u))`.

Conclude with `⟨_, p, hpm, rfl, hp⟩`. Take `⟨p, hpm, hpk, hp⟩` from `Nat.find_spec hex`. Establish `hc0 : p.coeff 0 ≠ 0`. Introduce `h0`. Take `⟨q, rfl⟩` from `Polynomial.X_dvd_iff.2 h0`.

Establish `hqm : q.Monic` using `Polynomial.monic_X.of_mul_monic_left hpm`. Establish `hdeg : (Polynomial.X * q).natDegree = q.natDegree + 1` using `Polynomial.natDegree_X_mul hqm.ne_zero`. Rewrite `hp` using `[Polynomial.eval₂_mul, Polynomial.eval₂_X, mul_eq_zero]`. Use `Nat.find_min hex (m := q.natDegree) (by omega) ⟨q, hqm, rfl, ?_⟩` and prove the remaining obligations. Conclude with `hp.resolve_left hv0`.

Establish `hQ : Ideal.Quotient.mk J (p.eval₂ (pullback A).toRingHom (linForm u)) = 0`. Rewrite using `[Polynomial.hom_eval₂]`. Conclude with `hp`. Establish `hQJ` using `Ideal.Quotient.eq_zero_iff_mem.1 hQ`. Use `⟨p.coeff 0, hc0, fun x hx hux => ?_⟩` and prove the remaining obligations.

Establish `h1 : eval x (p.eval₂ (pullback A).toRingHom (linForm u)) = 0` using `hx _ hQJ`. Rewrite `h1` using `[Polynomial.hom_eval₂, eval_linForm, hux, Polynomial.eval₂_at_zero]`. Establish `h2 : eval x (pullback A (p.coeff 0)) = 0` using `h1`. Rewrite `h2` using `[ComplexSets.eval_pullback]`. Then use the resulting hypothesis.
-/
theorem exists_poly_of_linForm {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {u : Fin n → ℂ} (hJ : J.IsPrime) (hA : IsFiniteProjection J A) (hu : linForm u ∉ J) :
    ∃ c : MvPolynomial (Fin d) ℂ, c ≠ 0 ∧
      ∀ x ∈ zeroSet J, linEval u x = 0 → eval (A *ᵥ x) c = 0 := by
  classical
  have hv0 : Ideal.Quotient.mk J (linForm u) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hu
  have hex : ∃ k, ∃ p : Polynomial (MvPolynomial (Fin d) ℂ), p.Monic ∧ p.natDegree = k ∧
      p.eval₂ (projHom J A).toRingHom (Ideal.Quotient.mk J (linForm u)) = 0 := by
    obtain ⟨p, hpm, hp⟩ := hA.finite.to_isIntegral (Ideal.Quotient.mk J (linForm u))
    exact ⟨_, p, hpm, rfl, hp⟩
  obtain ⟨p, hpm, hpk, hp⟩ := Nat.find_spec hex
  have hc0 : p.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.2 h0
    have hqm : q.Monic := Polynomial.monic_X.of_mul_monic_left hpm
    have hdeg : (Polynomial.X * q).natDegree = q.natDegree + 1 :=
      Polynomial.natDegree_X_mul hqm.ne_zero
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_X, mul_eq_zero] at hp
    refine Nat.find_min hex (m := q.natDegree) (by omega) ⟨q, hqm, rfl, ?_⟩
    exact hp.resolve_left hv0
  have hQ : Ideal.Quotient.mk J (p.eval₂ (pullback A).toRingHom (linForm u)) = 0 := by
    rw [Polynomial.hom_eval₂]; exact hp
  have hQJ := Ideal.Quotient.eq_zero_iff_mem.1 hQ
  refine ⟨p.coeff 0, hc0, fun x hx hux => ?_⟩
  have h1 : eval x (p.eval₂ (pullback A).toRingHom (linForm u)) = 0 := hx _ hQJ
  rw [Polynomial.hom_eval₂, eval_linForm, hux, Polynomial.eval₂_at_zero] at h1
  have h2 : eval x (pullback A (p.coeff 0)) = 0 := h1
  rwa [ComplexSets.eval_pullback] at h2

/- English proof (translation)
Take `⟨c, hc, hcz⟩` from `exists_poly_of_linForm hJ hA hu`. Use `measure_mono_null ?_ (DiscriminantSheetCover.volume_zero_set c hc)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, ⟨hx, hux⟩, rfl⟩`. Conclude with `hcz x hx hux`.
-/
theorem volume_image_zero {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {u : Fin n → ℂ} (hJ : J.IsPrime) (hA : IsFiniteProjection J A) (hu : linForm u ∉ J) :
    volume ((fun x => A *ᵥ x) '' {x | x ∈ zeroSet J ∧ linEval u x = 0}) = 0 := by
  obtain ⟨c, hc, hcz⟩ := exists_poly_of_linForm hJ hA hu
  refine measure_mono_null ?_ (DiscriminantSheetCover.volume_zero_set c hc)
  rintro _ ⟨x, ⟨hx, hux⟩, rfl⟩
  exact hcz x hx hux

/- English proof (translation)
The claim follows from `hsd.continuousOn.isOpen_inter_preimage hUs (hU.inter (isOpen_ne_fun (continuous_linEval u) continuous_const))`.
-/
theorem isOpen_dom {Us : Set (Fin d → ℂ)} {s : (Fin d → ℂ) → Fin n → ℂ} {U : Set (Fin n → ℂ)}
    (u : Fin n → ℂ) (hUs : IsOpen Us) (hsd : DifferentiableOn ℂ s Us) (hU : IsOpen U) :
    IsOpen (Us ∩ s ⁻¹' (U ∩ {x | linEval u x ≠ 0})) :=
  hsd.continuousOn.isOpen_inter_preimage hUs
    (hU.inter (isOpen_ne_fun (continuous_linEval u) continuous_const))

/- English proof (translation)
The claim follows from `SheetOnlyNull.differentiableOn_mulVec A' (s := Ψ ∘ s) (hΨ.comp (hsd.mono Set.inter_subset_left) fun _ hy => hy.2.1)`.
-/
theorem differentiableOn_tau {Us : Set (Fin d → ℂ)} {s : (Fin d → ℂ) → Fin n → ℂ} {U : Set (Fin n → ℂ)}
    {Ψ : (Fin n → ℂ) → Fin n → ℂ} (u : Fin n → ℂ) (A' : Matrix (Fin d) (Fin n) ℂ)
    (hsd : DifferentiableOn ℂ s Us) (hΨ : DifferentiableOn ℂ Ψ U) :
    DifferentiableOn ℂ (fun w => A' *ᵥ Ψ (s w)) (Us ∩ s ⁻¹' (U ∩ {x | linEval u x ≠ 0})) :=
  SheetOnlyNull.differentiableOn_mulVec A' (s := Ψ ∘ s)
    (hΨ.comp (hsd.mono Set.inter_subset_left) fun _ hy => hy.2.1)

/- English proof (translation)
Take `⟨Us, hUs, hyU, hsd, hsx, hsec, V, hV, hVs⟩` from `hs`. Establish `hxZ : x ∈ zeroSet J` using `hsx ▸ (hsec _ hyU).2`. Use `set D := Us ∩ s ⁻¹' (U ∩ {x | linEval u x ≠ 0}) with hDdef`. Establish `hD : IsOpen D` using `isOpen_dom u hUs hsd hU`. Establish `hyD : A *ᵥ x ∈ D` using `⟨hyU, by simp only [Set.mem_preimage, hsx]; exact ⟨hxU, hxu⟩⟩`.

Use `set F : (Fin d → ℂ) → Fin d → ℂ := fun w => A' *ᵥ Ψ (s w) with hFdef`. Establish `hFd : DifferentiableOn ℂ F D` using `differentiableOn_tau u A' hsd hΨ`. Establish `hΨsd : DifferentiableOn ℂ (fun w => Ψ (s w)) D` using `hΨ.comp (hsd.mono Set.inter_subset_left) fun _ hy => hy.2.1`. Establish `hFa` using `SheetOnlyNull.analyticOnNhd_of_differentiableOn hD hFd`. Use `set G : Set (Fin d → ℂ) := D ∩ (fun w => (ReciprocityTheory.AnForm.A.jacC F w).det) ⁻¹' {0}ᶜ with hGdef`.

Establish `hG : IsOpen G` using `(SheetOnlyNull.analyticOnNhd_det_jacC hD hFd).continuousOn |>.isOpen_inter_preimage hD isOpen_compl_singleton`. Establish `hinj : ∀ w, (ReciprocityTheory.AnForm.A.jacC F w).det ≠ 0 → Function.Injective (fderiv ℂ F w)` using `fun w hw => (SheetOnlyNull.injective_iff_det_ne_zero _).2 (by rwa [← ReciprocityTheory.AnForm.A.det_jacC])`. Establish `hequiv : ∀ w ∈ G, ∃ e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ), HasStrictFDerivAt F (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w`. Introduce `w hw`. Use `⟨(LinearEquiv.ofInjectiveEndo _ (hinj w hw.2)).toContinuousLinearEquiv, ?_⟩` and prove the remaining obligations.

Conclude with `(hFa w hw.1).hasStrictFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)`. Take `⟨e, he⟩` from `hequiv _ ⟨hyD, hdet⟩`. Use `set φ := he.toOpenPartialHomeomorph F with hφdef`. Establish `hφ : ∀ w, φ w = F w` using `fun w => by rw [hφdef, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]`. Establish `hysrc : A *ᵥ x ∈ φ.source` using `he.mem_toOpenPartialHomeomorph_source`.

Establish `hFx : F (A *ᵥ x) = A' *ᵥ Ψ x` using `by simp only [hFdef, hsx]`. Establish `hsym : φ.symm (A' *ᵥ Ψ x) = A *ᵥ x` using `by rw [← hFx, ← hφ, φ.left_inv hysrc]`. Establish `hP : Ψ x ∈ zeroSet J' \ {x | linEval u' x = 0}` using `hΨm ⟨hxZ, hxu⟩`. Establish `hΦc : ContinuousAt Φ (Ψ x)` using `(hΦ.differentiableAt (hU'.mem_nhds (hUsub' hP))).continuousAt`. Establish `hΦP : Φ (Ψ x) = x` using `hΦΨ x ⟨hxZ, hxu⟩`.

Use `⟨fun z => Ψ (s (φ.symm z)), φ.target ∩ φ.symm ⁻¹' G, φ.isOpen_inter_preimage_symm hG, ⟨by rw [← hFx, ← hφ]; exact φ.map_source hysrc, by rw [Set.mem_preimage, hsym]; exact ⟨hyD, hdet⟩⟩, ?_, by simp only [hsym, hsx], fun z hz => ⟨?_, (hΨm ⟨(hsec _ hz.2.1.1).2, hz.2.1.2.2⟩).1⟩, ?_⟩` and prove the remaining obligations. Introduce `z ⟨hzT, hzG⟩`. Take `⟨e', he'⟩` from `hequiv _ hzG`. Establish `hsymd : HasFDerivAt φ.symm _ z` using `φ.hasFDerivAt_symm hzT (f' := e') (by`. Establish `: (φ : (Fin d → ℂ) → Fin d → ℂ) = F` using `funext hφ`.

Rewrite using `[this]`. Conclude with `he'.hasFDerivAt)`. Conclude with `((hΨsd.differentiableAt (hD.mem_nhds hzG.1)).comp z hsymd.differentiableAt).differentiableWithinAt`. Use `show F (φ.symm z) = z`. Rewrite using `[← hφ, φ.right_inv hz.1]`.

Establish `hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z` using `by fun_prop`. Establish `hnx : V ∩ (fun z => A *ᵥ z) ⁻¹' (φ.source ∩ D) ∈ 𝓝 x` using `inter_mem hV (((φ.open_source.inter hD).preimage hAc).mem_nhds ⟨hysrc, hyD⟩)`. Use `⟨{z | linEval u' z ≠ 0} ∩ Φ ⁻¹' (V ∩ (fun z => A *ᵥ z) ⁻¹' (φ.source ∩ D)), inter_mem ((isOpen_ne_fun (continuous_linEval u') continuous_const).mem_nhds hP.2) (hΦc.preimage_mem_nhds (by rw [hΦP]; exact hnx)), ?_⟩` and prove the remaining obligations. Introduce and unpack `x'' ⟨hx''Z, hx''u, hx''V, hx''src, hx''D⟩ -`. Establish `hx''P : x'' ∈ zeroSet J' \ {x | linEval u' x = 0}` using `⟨hx''Z, hx''u⟩`.

Establish `hx'' : Φ x'' = s (A *ᵥ Φ x'')` using `hVs _ ⟨(hΦm hx''P).1, hx''V⟩ hx''D.1`. Establish `hA' : A' *ᵥ x'' = φ (A *ᵥ Φ x'')`. Rewrite using `[hφ, hFdef]`. Use `show A' *ᵥ x'' = A' *ᵥ Ψ (s (A *ᵥ Φ x''))`. Rewrite using `[← hx'', hΨΦ x'' hx''P]`.

Use `show x'' = Ψ (s (φ.symm (A' *ᵥ x'')))`. Rewrite using `[hA', φ.left_inv hx''src, ← hx'', hΨΦ x'' hx''P]`.
-/
theorem exists_sheet_of_det_ne_zero {J J' : Ideal (MvPolynomial (Fin n) ℂ)}
    {A A' : Matrix (Fin d) (Fin n) ℂ} {u u' : Fin n → ℂ} {U U' : Set (Fin n → ℂ)}
    {Φ Ψ : (Fin n → ℂ) → Fin n → ℂ} (hU : IsOpen U) (hU' : IsOpen U')
    (hUsub' : zeroSet J' \ {x | linEval u' x = 0} ⊆ U')
    (hΦ : DifferentiableOn ℂ Φ U') (hΨ : DifferentiableOn ℂ Ψ U)
    (hΦm : Set.MapsTo Φ (zeroSet J' \ {x | linEval u' x = 0}) (zeroSet J \ {x | linEval u x = 0}))
    (hΨm : Set.MapsTo Ψ (zeroSet J \ {x | linEval u x = 0}) (zeroSet J' \ {x | linEval u' x = 0}))
    (hΨΦ : ∀ x ∈ zeroSet J' \ {x | linEval u' x = 0}, Ψ (Φ x) = x)
    (hΦΨ : ∀ x ∈ zeroSet J \ {x | linEval u x = 0}, Φ (Ψ x) = x)
    {x : Fin n → ℂ} (hxu : linEval u x ≠ 0) (hxU : x ∈ U) {s : (Fin d → ℂ) → Fin n → ℂ}
    (hs : IsSheetAt J A x s)
    (hdet : (ReciprocityTheory.AnForm.A.jacC (fun w => A' *ᵥ Ψ (s w)) (A *ᵥ x)).det ≠ 0) :
    ∃ s', IsSheetAt J' A' (Ψ x) s' := by
  obtain ⟨Us, hUs, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hs
  have hxZ : x ∈ zeroSet J := hsx ▸ (hsec _ hyU).2
  set D := Us ∩ s ⁻¹' (U ∩ {x | linEval u x ≠ 0}) with hDdef
  have hD : IsOpen D := isOpen_dom u hUs hsd hU
  have hyD : A *ᵥ x ∈ D := ⟨hyU, by simp only [Set.mem_preimage, hsx]; exact ⟨hxU, hxu⟩⟩
  set F : (Fin d → ℂ) → Fin d → ℂ := fun w => A' *ᵥ Ψ (s w) with hFdef
  have hFd : DifferentiableOn ℂ F D := differentiableOn_tau u A' hsd hΨ
  have hΨsd : DifferentiableOn ℂ (fun w => Ψ (s w)) D :=
    hΨ.comp (hsd.mono Set.inter_subset_left) fun _ hy => hy.2.1
  have hFa := SheetOnlyNull.analyticOnNhd_of_differentiableOn hD hFd
  set G : Set (Fin d → ℂ) := D ∩ (fun w => (ReciprocityTheory.AnForm.A.jacC F w).det) ⁻¹' {0}ᶜ with hGdef
  have hG : IsOpen G := (SheetOnlyNull.analyticOnNhd_det_jacC hD hFd).continuousOn
    |>.isOpen_inter_preimage hD isOpen_compl_singleton
  have hinj : ∀ w, (ReciprocityTheory.AnForm.A.jacC F w).det ≠ 0 → Function.Injective (fderiv ℂ F w) :=
    fun w hw => (SheetOnlyNull.injective_iff_det_ne_zero _).2 (by rwa [← ReciprocityTheory.AnForm.A.det_jacC])
  have hequiv : ∀ w ∈ G, ∃ e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ),
      HasStrictFDerivAt F (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w := by
    intro w hw
    refine ⟨(LinearEquiv.ofInjectiveEndo _ (hinj w hw.2)).toContinuousLinearEquiv, ?_⟩
    exact (hFa w hw.1).hasStrictFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  obtain ⟨e, he⟩ := hequiv _ ⟨hyD, hdet⟩
  set φ := he.toOpenPartialHomeomorph F with hφdef
  have hφ : ∀ w, φ w = F w := fun w => by rw [hφdef, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
  have hysrc : A *ᵥ x ∈ φ.source := he.mem_toOpenPartialHomeomorph_source
  have hFx : F (A *ᵥ x) = A' *ᵥ Ψ x := by simp only [hFdef, hsx]
  have hsym : φ.symm (A' *ᵥ Ψ x) = A *ᵥ x := by rw [← hFx, ← hφ, φ.left_inv hysrc]
  have hP : Ψ x ∈ zeroSet J' \ {x | linEval u' x = 0} := hΨm ⟨hxZ, hxu⟩
  have hΦc : ContinuousAt Φ (Ψ x) := (hΦ.differentiableAt (hU'.mem_nhds (hUsub' hP))).continuousAt
  have hΦP : Φ (Ψ x) = x := hΦΨ x ⟨hxZ, hxu⟩
  refine ⟨fun z => Ψ (s (φ.symm z)), φ.target ∩ φ.symm ⁻¹' G, φ.isOpen_inter_preimage_symm hG,
    ⟨by rw [← hFx, ← hφ]; exact φ.map_source hysrc, by rw [Set.mem_preimage, hsym]; exact ⟨hyD, hdet⟩⟩,
    ?_, by simp only [hsym, hsx], fun z hz => ⟨?_, (hΨm ⟨(hsec _ hz.2.1.1).2, hz.2.1.2.2⟩).1⟩, ?_⟩
  · intro z ⟨hzT, hzG⟩
    obtain ⟨e', he'⟩ := hequiv _ hzG
    have hsymd : HasFDerivAt φ.symm _ z :=
      φ.hasFDerivAt_symm hzT (f' := e') (by
        have : (φ : (Fin d → ℂ) → Fin d → ℂ) = F := funext hφ
        rw [this]; exact he'.hasFDerivAt)
    exact ((hΨsd.differentiableAt (hD.mem_nhds hzG.1)).comp z
      hsymd.differentiableAt).differentiableWithinAt
  · show F (φ.symm z) = z
    rw [← hφ, φ.right_inv hz.1]
  · have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
    have hnx : V ∩ (fun z => A *ᵥ z) ⁻¹' (φ.source ∩ D) ∈ 𝓝 x :=
      inter_mem hV (((φ.open_source.inter hD).preimage hAc).mem_nhds ⟨hysrc, hyD⟩)
    refine ⟨{z | linEval u' z ≠ 0} ∩ Φ ⁻¹' (V ∩ (fun z => A *ᵥ z) ⁻¹' (φ.source ∩ D)),
      inter_mem ((isOpen_ne_fun (continuous_linEval u') continuous_const).mem_nhds hP.2)
        (hΦc.preimage_mem_nhds (by rw [hΦP]; exact hnx)), ?_⟩
    rintro x'' ⟨hx''Z, hx''u, hx''V, hx''src, hx''D⟩ -
    have hx''P : x'' ∈ zeroSet J' \ {x | linEval u' x = 0} := ⟨hx''Z, hx''u⟩
    have hx'' : Φ x'' = s (A *ᵥ Φ x'') := hVs _ ⟨(hΦm hx''P).1, hx''V⟩ hx''D.1
    have hA' : A' *ᵥ x'' = φ (A *ᵥ Φ x'') := by
      rw [hφ, hFdef]
      show A' *ᵥ x'' = A' *ᵥ Ψ (s (A *ᵥ Φ x''))
      rw [← hx'', hΨΦ x'' hx''P]
    show x'' = Ψ (s (φ.symm (A' *ᵥ x'')))
    rw [hA', φ.left_inv hx''src, ← hx'', hΨΦ x'' hx''P]

/- English proof (translation)
Take `⟨Us, hUs, hyU, hsd, hsx, hsec, V, hV, hVs⟩` from `hs`. Establish `hxZ : x ∈ zeroSet J` using `hsx ▸ (hsec _ hyU).2`. Use `set D := Us ∩ s ⁻¹' (U ∩ {x | linEval u x ≠ 0}) with hDdef`. Establish `hD : IsOpen D` using `isOpen_dom u hUs hsd hU`. Use `set F : (Fin d → ℂ) → Fin d → ℂ := fun w => A' *ᵥ Ψ (s w) with hFdef`.

Establish `hFd : DifferentiableOn ℂ F D` using `differentiableOn_tau u A' hsd hΨ`. Assume the negation of the conclusion as `hall`. Use `push Not at hall`. Establish `hcrit : F '' (W₀ ∩ D) ⊆ F '' {w | w ∈ D ∧ ¬ Function.Injective (fderiv ℂ F w)}` using `Set.image_mono fun w hw => ⟨hw.2, fun hinj => (SheetOnlyNull.injective_iff_det_ne_zero _).1 hinj (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hall w hw.1)⟩`. Establish `hnull` using `measure_mono_null hcrit (h₂ d d D F hD hFd)`.

Establish `hP : Ψ x ∈ zeroSet J' \ {x | linEval u' x = 0}` using `hΨm ⟨hxZ, hxu⟩`. Establish `hΦc : ContinuousAt Φ (Ψ x)` using `(hΦ.differentiableAt (hU'.mem_nhds (hUsub' hP))).continuousAt`. Establish `hΦP : Φ (Ψ x) = x` using `hΦΨ x ⟨hxZ, hxu⟩`. Establish `hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z` using `by fun_prop`. Establish `hnx : V ∩ (fun z => A *ᵥ z) ⁻¹' (W₀ ∩ D) ∈ 𝓝 x` using `inter_mem hV (((hW₀.inter hD).preimage hAc).mem_nhds ⟨hxW₀, hyU, by simp only [Set.mem_preimage, hsx]; exact ⟨hxU, hxu⟩⟩)`.

Establish `hN : {z | linEval u' z ≠ 0} ∩ Φ ⁻¹' (V ∩ (fun z => A *ᵥ z) ⁻¹' (W₀ ∩ D)) ∈ 𝓝 (Ψ x)` using `inter_mem ((isOpen_ne_fun (continuous_linEval u') continuous_const).mem_nhds hP.2) (hΦc.preimage_mem_nhds (by rw [hΦP]; exact hnx))`. Establish `hnhds` using `h₁ n d J' (linPoly A') hJ' hA'.injective hA'.finite (Ψ x) hP.1 _ hN`. Establish `hev : ∀ z : Fin n → ℂ, (fun i => eval z (linPoly A' i)) = A' *ᵥ z` using `fun z => by`. Use extensionality with `i`. Simplify using `[linPoly, Matrix.mulVec, dotProduct]`.

Simplify using `only [hev] at hnhds`. Establish `hsub : (fun z => A' *ᵥ z) '' (IndefiniteRowSideFullHecke.ComplexSets.zeroLocus J' ∩ ({z | linEval u' z ≠ 0} ∩ Φ ⁻¹' (V ∩ (fun z => A *ᵥ z) ⁻¹' (W₀ ∩ D)))) ⊆ F '' (W₀ ∩ D)`. Introduce and unpack `_ ⟨z, ⟨hzZ, hzu, hzV, hzW⟩, rfl⟩`. Establish `hzP : z ∈ zeroSet J' \ {x | linEval u' x = 0}` using `⟨hzZ, hzu⟩`. Use `⟨A *ᵥ Φ z, hzW, ?_⟩` and prove the remaining obligations.

Use `show A' *ᵥ Ψ (s (A *ᵥ Φ z)) = A' *ᵥ z`. Rewrite using `[← hVs (Φ z) ⟨(hΦm hzP).1, hzV⟩ hzW.2.1, hΨΦ z hzP]`. Establish `hpos` using `Measure.measure_pos_of_mem_nhds (μ := μH[(Module.finrank ℝ (Fin d → ℂ) : ℝ)]) (Filter.mem_of_superset hnhds hsub)`. Rewrite `hpos` using `[SheetOnlyNull.finrank_real_fin_complex]`. Conclude with `hpos.ne' hnull`.
-/
theorem exists_det_ne_zero (h₁ : IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement) {J J' : Ideal (MvPolynomial (Fin n) ℂ)}
    {A A' : Matrix (Fin d) (Fin n) ℂ} {u u' : Fin n → ℂ} {U U' : Set (Fin n → ℂ)}
    {Φ Ψ : (Fin n → ℂ) → Fin n → ℂ} (hJ' : J'.IsPrime) (hA' : IsFiniteProjection J' A')
    (hU : IsOpen U) (hU' : IsOpen U')
    (hUsub' : zeroSet J' \ {x | linEval u' x = 0} ⊆ U')
    (hΦ : DifferentiableOn ℂ Φ U') (hΨ : DifferentiableOn ℂ Ψ U)
    (hΦm : Set.MapsTo Φ (zeroSet J' \ {x | linEval u' x = 0}) (zeroSet J \ {x | linEval u x = 0}))
    (hΨm : Set.MapsTo Ψ (zeroSet J \ {x | linEval u x = 0}) (zeroSet J' \ {x | linEval u' x = 0}))
    (hΨΦ : ∀ x ∈ zeroSet J' \ {x | linEval u' x = 0}, Ψ (Φ x) = x)
    (hΦΨ : ∀ x ∈ zeroSet J \ {x | linEval u x = 0}, Φ (Ψ x) = x)
    {x : Fin n → ℂ} (hxu : linEval u x ≠ 0) (hxU : x ∈ U) {s : (Fin d → ℂ) → Fin n → ℂ}
    (hs : IsSheetAt J A x s) {W₀ : Set (Fin d → ℂ)} (hW₀ : IsOpen W₀) (hxW₀ : A *ᵥ x ∈ W₀) :
    ∃ w ∈ W₀, (ReciprocityTheory.AnForm.A.jacC (fun w => A' *ᵥ Ψ (s w)) w).det ≠ 0 := by
  obtain ⟨Us, hUs, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hs
  have hxZ : x ∈ zeroSet J := hsx ▸ (hsec _ hyU).2
  set D := Us ∩ s ⁻¹' (U ∩ {x | linEval u x ≠ 0}) with hDdef
  have hD : IsOpen D := isOpen_dom u hUs hsd hU
  set F : (Fin d → ℂ) → Fin d → ℂ := fun w => A' *ᵥ Ψ (s w) with hFdef
  have hFd : DifferentiableOn ℂ F D := differentiableOn_tau u A' hsd hΨ
  by_contra hall
  push Not at hall
  have hcrit : F '' (W₀ ∩ D) ⊆ F '' {w | w ∈ D ∧ ¬ Function.Injective (fderiv ℂ F w)} :=
    Set.image_mono fun w hw => ⟨hw.2, fun hinj => (SheetOnlyNull.injective_iff_det_ne_zero _).1 hinj
      (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hall w hw.1)⟩
  have hnull := measure_mono_null hcrit (h₂ d d D F hD hFd)
  have hP : Ψ x ∈ zeroSet J' \ {x | linEval u' x = 0} := hΨm ⟨hxZ, hxu⟩
  have hΦc : ContinuousAt Φ (Ψ x) := (hΦ.differentiableAt (hU'.mem_nhds (hUsub' hP))).continuousAt
  have hΦP : Φ (Ψ x) = x := hΦΨ x ⟨hxZ, hxu⟩
  have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
  have hnx : V ∩ (fun z => A *ᵥ z) ⁻¹' (W₀ ∩ D) ∈ 𝓝 x :=
    inter_mem hV (((hW₀.inter hD).preimage hAc).mem_nhds
      ⟨hxW₀, hyU, by simp only [Set.mem_preimage, hsx]; exact ⟨hxU, hxu⟩⟩)
  have hN : {z | linEval u' z ≠ 0} ∩ Φ ⁻¹' (V ∩ (fun z => A *ᵥ z) ⁻¹' (W₀ ∩ D)) ∈ 𝓝 (Ψ x) :=
    inter_mem ((isOpen_ne_fun (continuous_linEval u') continuous_const).mem_nhds hP.2)
      (hΦc.preimage_mem_nhds (by rw [hΦP]; exact hnx))
  have hnhds := h₁ n d J' (linPoly A') hJ' hA'.injective hA'.finite (Ψ x) hP.1 _ hN
  have hev : ∀ z : Fin n → ℂ, (fun i => eval z (linPoly A' i)) = A' *ᵥ z := fun z => by
    ext i
    simp [linPoly, Matrix.mulVec, dotProduct]
  simp only [hev] at hnhds
  have hsub : (fun z => A' *ᵥ z) '' (IndefiniteRowSideFullHecke.ComplexSets.zeroLocus J' ∩
      ({z | linEval u' z ≠ 0} ∩ Φ ⁻¹' (V ∩ (fun z => A *ᵥ z) ⁻¹' (W₀ ∩ D)))) ⊆ F '' (W₀ ∩ D) := by
    rintro _ ⟨z, ⟨hzZ, hzu, hzV, hzW⟩, rfl⟩
    have hzP : z ∈ zeroSet J' \ {x | linEval u' x = 0} := ⟨hzZ, hzu⟩
    refine ⟨A *ᵥ Φ z, hzW, ?_⟩
    show A' *ᵥ Ψ (s (A *ᵥ Φ z)) = A' *ᵥ z
    rw [← hVs (Φ z) ⟨(hΦm hzP).1, hzV⟩ hzW.2.1, hΨΦ z hzP]
  have hpos := Measure.measure_pos_of_mem_nhds (μ := μH[(Module.finrank ℝ (Fin d → ℂ) : ℝ)])
    (Filter.mem_of_superset hnhds hsub)
  rw [SheetOnlyNull.finrank_real_fin_complex] at hpos
  exact hpos.ne' hnull

end ChartChangeSheetNull

open ChartChangeSheetNull in

/- English proof (translation)
Introduce `n d J J' A A' u u' U U' Φ Ψ hJ _ hJ' _ hu _ hA hA' hU hU' hUsub hUsub' hΦ hΨ hΦm hΨm hΨΦ hΦΨ`. Use `set B := {x | x ∈ zeroSet J ∧ (∃ s, IsSheetAt J A x s) ∧ linEval u x ≠ 0 ∧ ¬ ∃ s', IsSheetAt J' A' (Ψ x) s'} with hBdef`. Use `choose σ Us W hUs hW hσd hWsh hxW using fun x : Fin n → ℂ => SheetOnlyNull.exists_sheet_nhds (J := J) (A := A) x`. Take `⟨T, hTc, hTU⟩` from `TopologicalSpace.isOpen_iUnion_countable W hW`. Establish `hpiece : ∀ i, volume ((fun x => A *ᵥ x) '' (B ∩ W i)) = 0`.

Introduce `i`. Apply `ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, ⟨hxB, hxWi⟩, rfl⟩`. Take `⟨hAx, hsh⟩` from `hWsh i x ⟨hxB.1, hxWi⟩`. Establish `hxU : x ∈ U` using `hUsub ⟨hxB.1, hxB.2.2.1⟩`.

Establish `hD` using `isOpen_dom u (hUs i) (hσd i) hU`. Establish `hsx : σ i (A *ᵥ x) = x` using `by obtain ⟨_, _, _, _, h, _⟩ := hsh; exact h`. Establish `hAxD : A *ᵥ x ∈ Us i ∩ σ i ⁻¹' (U ∩ {x | linEval u x ≠ 0})` using `⟨hAx, by simp only [Set.mem_preimage, hsx]; exact ⟨hxU, hxB.2.2.1⟩⟩`. Take `⟨r, hr, hball⟩` from `Metric.isOpen_iff.mp hD _ hAxD`. Use `⟨Metric.ball (A *ᵥ x) r, Metric.isOpen_ball, Metric.mem_ball_self hr, (convex_ball _ r).isPreconnected, fun w => (ReciprocityTheory.AnForm.A.jacC (fun v => A' *ᵥ Ψ (σ i v)) w).det, (SheetOnlyNull.analyticOnNhd_det_jacC hD (differentiableOn_tau u A' (hσd i) hΨ)).mono hball, exists …` and prove the remaining obligations.

Introduce and unpack `_ ⟨⟨x'', ⟨hx''B, hx''W⟩, rfl⟩, -⟩`. Assume the negation of the conclusion as `hne`. Conclude with `hx''B.2.2.2 (exists_sheet_of_det_ne_zero hU hU' hUsub' hΦ hΨ hΦm hΨm hΨΦ hΦΨ hx''B.2.2.1 (hUsub ⟨hx''B.1, hx''B.2.2.1⟩) (hWsh i x'' ⟨hx''B.1, hx''W⟩).2 hne)`. Establish `hBnull : volume ((fun x => A *ᵥ x) '' B) = 0`. Use `measure_mono_null ?_ ((measure_biUnion_null_iff hTc).2 fun i _ => hpiece i)` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, hxB, rfl⟩`. Establish `hx : x ∈ ⋃ i ∈ T, W i` using `hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x hxB.2.1⟩`. Take `⟨i, hiT, hxi⟩` from `Set.mem_iUnion₂.1 hx`. Conclude with `Set.mem_biUnion hiT ⟨x, ⟨hxB, hxi⟩, rfl⟩`. Use `measure_mono_null ?_ (measure_union_null hBnull (volume_image_zero hJ hA hu))` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, ⟨hxZ, hxs, hnot⟩, rfl⟩`. Distinguish the cases in `hux : linEval u x = 0`. Conclude with `Or.inr ⟨x, ⟨hxZ, hux⟩, rfl⟩`. Conclude with `Or.inl ⟨x, ⟨hxZ, hxs, hux, fun h => hnot ⟨hux, h⟩⟩, rfl⟩`.
-/
theorem ChartChangeSheetNull.proof (h₁ : IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement) : ChartChangeSheetNull.Statement := by
  intro n d J J' A A' u u' U U' Φ Ψ hJ _ hJ' _ hu _ hA hA' hU hU' hUsub hUsub' hΦ hΨ hΦm hΨm hΨΦ hΦΨ
  set B := {x | x ∈ zeroSet J ∧ (∃ s, IsSheetAt J A x s) ∧ linEval u x ≠ 0 ∧
    ¬ ∃ s', IsSheetAt J' A' (Ψ x) s'} with hBdef
  choose σ Us W hUs hW hσd hWsh hxW using
    fun x : Fin n → ℂ => SheetOnlyNull.exists_sheet_nhds (J := J) (A := A) x
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  have hpiece : ∀ i, volume ((fun x => A *ᵥ x) '' (B ∩ W i)) = 0 := by
    intro i
    apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
    rintro _ ⟨x, ⟨hxB, hxWi⟩, rfl⟩
    obtain ⟨hAx, hsh⟩ := hWsh i x ⟨hxB.1, hxWi⟩
    have hxU : x ∈ U := hUsub ⟨hxB.1, hxB.2.2.1⟩
    have hD := isOpen_dom u (hUs i) (hσd i) hU
    have hsx : σ i (A *ᵥ x) = x := by obtain ⟨_, _, _, _, h, _⟩ := hsh; exact h
    have hAxD : A *ᵥ x ∈ Us i ∩ σ i ⁻¹' (U ∩ {x | linEval u x ≠ 0}) :=
      ⟨hAx, by simp only [Set.mem_preimage, hsx]; exact ⟨hxU, hxB.2.2.1⟩⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hD _ hAxD
    refine ⟨Metric.ball (A *ᵥ x) r, Metric.isOpen_ball, Metric.mem_ball_self hr,
      (convex_ball _ r).isPreconnected,
      fun w => (ReciprocityTheory.AnForm.A.jacC (fun v => A' *ᵥ Ψ (σ i v)) w).det,
      (SheetOnlyNull.analyticOnNhd_det_jacC hD (differentiableOn_tau u A' (hσd i) hΨ)).mono hball,
      exists_det_ne_zero h₁ h₂ hJ' hA' hU hU' hUsub' hΦ hΨ hΦm hΨm hΨΦ hΦΨ hxB.2.2.1 hxU hsh
        Metric.isOpen_ball (Metric.mem_ball_self hr), ?_⟩
    rintro _ ⟨⟨x'', ⟨hx''B, hx''W⟩, rfl⟩, -⟩
    by_contra hne
    exact hx''B.2.2.2 (exists_sheet_of_det_ne_zero hU hU' hUsub' hΦ hΨ hΦm hΨm hΨΦ hΦΨ hx''B.2.2.1
      (hUsub ⟨hx''B.1, hx''B.2.2.1⟩) (hWsh i x'' ⟨hx''B.1, hx''W⟩).2 hne)
  have hBnull : volume ((fun x => A *ᵥ x) '' B) = 0 := by
    refine measure_mono_null ?_ ((measure_biUnion_null_iff hTc).2 fun i _ => hpiece i)
    rintro _ ⟨x, hxB, rfl⟩
    have hx : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x hxB.2.1⟩
    obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 hx
    exact Set.mem_biUnion hiT ⟨x, ⟨hxB, hxi⟩, rfl⟩
  refine measure_mono_null ?_ (measure_union_null hBnull (volume_image_zero hJ hA hu))
  rintro _ ⟨x, ⟨hxZ, hxs, hnot⟩, rfl⟩
  by_cases hux : linEval u x = 0
  · exact Or.inr ⟨x, ⟨hxZ, hux⟩, rfl⟩
  · exact Or.inl ⟨x, ⟨hxZ, hxs, hux, fun h => hnot ⟨hux, h⟩⟩, rfl⟩

end

end GroundTheory.Heights₂.Heights

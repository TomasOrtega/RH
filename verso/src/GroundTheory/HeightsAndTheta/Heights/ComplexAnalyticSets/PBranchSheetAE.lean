import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchSheetAE
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRankDeficientFibreInfinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDiscriminantSheetCover
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetOnlyNull
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace BranchSheetAE

variable {d : ℕ}

/- English proof (translation)
Establish `hFa` using `SheetOnlyNull.analyticOnNhd_of_differentiableOn hG hF`. Establish `hequiv : ∀ w ∈ G, ∃ e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ), HasStrictFDerivAt F (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w`. Introduce `w hw`. Establish `hinj : Function.Injective (fderiv ℂ F w)` using `(SheetOnlyNull.injective_iff_det_ne_zero _).2 (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hdet w hw)`. Use `⟨(LinearEquiv.ofInjectiveEndo _ hinj).toContinuousLinearEquiv, ?_⟩` and prove the remaining obligations.

Conclude with `(hFa w hw).hasStrictFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)`. Apply `measure_null_of_locally_null` to reduce the goal to its premises. Introduce and unpack `x ⟨hxG, -⟩`. Take `⟨e, he⟩` from `hequiv x hxG`. Use `set φ := he.toOpenPartialHomeomorph F with hφdef`.

Establish `hφ : ∀ w, φ w = F w` using `fun w => by rw [hφdef, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]`. Establish `hsymd : DifferentiableOn ℝ φ.symm (φ.target ∩ φ.symm ⁻¹' G)`. Introduce and unpack `z ⟨hzT, hzG⟩`. Take `⟨e', he'⟩` from `hequiv _ hzG`. Establish `hd : HasFDerivAt φ.symm _ z` using `φ.hasFDerivAt_symm hzT (f' := e') (by`.

Establish `: (φ : (Fin d → ℂ) → Fin d → ℂ) = F` using `funext hφ`. Rewrite using `[this]`. Conclude with `he'.hasFDerivAt)`. Conclude with `(hd.differentiableAt.restrictScalars ℝ).differentiableWithinAt`. Use `⟨{t | t ∈ G ∧ F t ∈ N} ∩ φ.source, inter_mem_nhdsWithin _ (φ.open_source.mem_nhds he.mem_toOpenPartialHomeomorph_source), ?_⟩` and prove the remaining obligations.

Use `measure_mono_null ?_ (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero (μ := volume) (hsymd.mono Set.inter_subset_left) (measure_mono_null Set.inter_subset_right hN))` and prove the remaining obligations. Introduce and unpack `t ⟨⟨htG, htN⟩, hts⟩`. Use `⟨φ t, ⟨⟨φ.map_source hts, ?_⟩, ?_⟩, φ.left_inv hts⟩` and prove the remaining obligations. Use `show φ.symm (φ t) ∈ G`. Rewrite using `[φ.left_inv hts]`.

Conclude with `htG`. Rewrite using `[hφ]`. Conclude with `htN`.
-/
theorem volume_preimage_null {G : Set (Fin d → ℂ)} {F : (Fin d → ℂ) → Fin d → ℂ} (hG : IsOpen G)
    (hF : DifferentiableOn ℂ F G) (hdet : ∀ w ∈ G, (ReciprocityTheory.AnForm.A.jacC F w).det ≠ 0)
    {N : Set (Fin d → ℂ)} (hN : volume N = 0) :
    volume {t | t ∈ G ∧ F t ∈ N} = 0 := by
  have hFa := SheetOnlyNull.analyticOnNhd_of_differentiableOn hG hF
  have hequiv : ∀ w ∈ G, ∃ e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ),
      HasStrictFDerivAt F (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w := by
    intro w hw
    have hinj : Function.Injective (fderiv ℂ F w) :=
      (SheetOnlyNull.injective_iff_det_ne_zero _).2 (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hdet w hw)
    refine ⟨(LinearEquiv.ofInjectiveEndo _ hinj).toContinuousLinearEquiv, ?_⟩
    exact (hFa w hw).hasStrictFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  apply measure_null_of_locally_null
  rintro x ⟨hxG, -⟩
  obtain ⟨e, he⟩ := hequiv x hxG
  set φ := he.toOpenPartialHomeomorph F with hφdef
  have hφ : ∀ w, φ w = F w := fun w => by rw [hφdef, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
  have hsymd : DifferentiableOn ℝ φ.symm (φ.target ∩ φ.symm ⁻¹' G) := by
    rintro z ⟨hzT, hzG⟩
    obtain ⟨e', he'⟩ := hequiv _ hzG
    have hd : HasFDerivAt φ.symm _ z :=
      φ.hasFDerivAt_symm hzT (f' := e') (by
        have : (φ : (Fin d → ℂ) → Fin d → ℂ) = F := funext hφ
        rw [this]; exact he'.hasFDerivAt)
    exact (hd.differentiableAt.restrictScalars ℝ).differentiableWithinAt
  refine ⟨{t | t ∈ G ∧ F t ∈ N} ∩ φ.source,
    inter_mem_nhdsWithin _ (φ.open_source.mem_nhds he.mem_toOpenPartialHomeomorph_source), ?_⟩
  refine measure_mono_null ?_ (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (μ := volume) (hsymd.mono Set.inter_subset_left) (measure_mono_null Set.inter_subset_right hN))
  rintro t ⟨⟨htG, htN⟩, hts⟩
  refine ⟨φ t, ⟨⟨φ.map_source hts, ?_⟩, ?_⟩, φ.left_inv hts⟩
  · show φ.symm (φ t) ∈ G
    rw [φ.left_inv hts]; exact htG
  · rw [hφ]; exact htN

end BranchSheetAE

/- English proof (translation)
Introduce `n d J A p γ hJ hdim hA`. Use `set Δ := Metric.ball (0 : Fin d → ℂ) γ.radius with hΔ`. Use `set τ : (Fin d → ℂ) → Fin d → ℂ := fun t => A *ᵥ γ.toFun t with hτdef`. Establish `hΔo : IsOpen Δ` using `Metric.isOpen_ball`. Establish `hτd : DifferentiableOn ℂ τ Δ` using `SheetOnlyNull.differentiableOn_mulVec A γ.differentiableOn`.

Establish `hdeta` using `SheetOnlyNull.analyticOnNhd_det_jacC hΔo hτd`. Establish `hne : ∃ z ∈ Δ, (ReciprocityTheory.AnForm.A.jacC τ z).det ≠ 0`. Assume the negation of the conclusion as `hall`. Use `push Not at hall`. Take `⟨y, hy⟩` from `h₁ d d Δ τ hΔo ⟨0, Metric.mem_ball_self γ.radius_pos⟩ hτd fun v hv hinj => (SheetOnlyNull.injective_iff_det_ne_zero _).1 hinj (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hall v hv)`.

Establish `hinf : (γ.toFun '' {t | t ∈ Δ ∧ τ t = y}).Infinite` using `(Set.infinite_image_iff (γ.injOn.mono fun t ht => ht.1)).2 hy`. Use `hinf ((h₂ n d J A hJ hdim hA y).2.1.subset ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨t, ⟨htΔ, hty⟩, rfl⟩`. Conclude with `⟨γ.mapsTo htΔ, hty⟩`. Establish `hZ` using `ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd hΔo (convex_ball _ _).isPreconnected hdeta hne`.

Take `⟨P, U, D, N, s, -, hUD, -, -, hnull, hfib⟩` from `h₃ n d J A hJ hdim hA`. Use `set G := Δ ∩ (fun t => (ReciprocityTheory.AnForm.A.jacC τ t).det) ⁻¹' {0}ᶜ with hGdef`. Establish `hG : IsOpen G` using `hdeta.continuousOn.isOpen_inter_preimage hΔo isOpen_compl_singleton`. Establish `hS` using `BranchSheetAE.volume_preimage_null hG (hτd.mono Set.inter_subset_left) (fun w hw => hw.2) hnull`. Rewrite using `[ae_restrict_iff' hΔo.measurableSet, ae_iff]`.

Use `measure_mono_null ?_ (measure_union_null hZ hS)` and prove the remaining obligations. Introduce `t ht`. Simplify using `only [Set.mem_ofPred_eq, Classical.not_imp] at ht`. Take `⟨htΔ, hno⟩` from `ht`. Distinguish the cases in `hdt : (ReciprocityTheory.AnForm.A.jacC τ t).det = 0`.

Conclude with `Or.inl ⟨htΔ, hdt⟩`. Use `Or.inr ⟨⟨htΔ, hdt⟩, fun hD => hno ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `Set.mem_iUnion.1 hD`. Take `⟨hfibk, -, hsh⟩` from `hfib k (τ t) ((hUD k).2.2.1 hk)`. Establish `hmem : γ.toFun t ∈ fibre J A (τ t)` using `⟨γ.mapsTo htΔ, rfl⟩`.

Rewrite `hmem` using `[hfibk]`. Take `⟨j, hj⟩` from `hmem`. Conclude with `⟨s k j, hj ▸ hsh j⟩`.
-/
theorem BranchSheetAE.proof (h₁ : IndefiniteRowSideFullHecke.ComplexSets.RankDeficientFibreInfinite.Statement)
    (h₂ : ComplexSets.FibreBound.Statement) (h₃ : DiscriminantSheetCover.Statement) :
    BranchSheetAE.Statement := by
  intro n d J A p γ hJ hdim hA
  set Δ := Metric.ball (0 : Fin d → ℂ) γ.radius with hΔ
  set τ : (Fin d → ℂ) → Fin d → ℂ := fun t => A *ᵥ γ.toFun t with hτdef
  have hΔo : IsOpen Δ := Metric.isOpen_ball
  have hτd : DifferentiableOn ℂ τ Δ := SheetOnlyNull.differentiableOn_mulVec A γ.differentiableOn
  have hdeta := SheetOnlyNull.analyticOnNhd_det_jacC hΔo hτd
  have hne : ∃ z ∈ Δ, (ReciprocityTheory.AnForm.A.jacC τ z).det ≠ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨y, hy⟩ := h₁ d d Δ τ hΔo ⟨0, Metric.mem_ball_self γ.radius_pos⟩ hτd fun v hv hinj =>
      (SheetOnlyNull.injective_iff_det_ne_zero _).1 hinj
        (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hall v hv)
    have hinf : (γ.toFun '' {t | t ∈ Δ ∧ τ t = y}).Infinite :=
      (Set.infinite_image_iff (γ.injOn.mono fun t ht => ht.1)).2 hy
    refine hinf ((h₂ n d J A hJ hdim hA y).2.1.subset ?_)
    rintro _ ⟨t, ⟨htΔ, hty⟩, rfl⟩
    exact ⟨γ.mapsTo htΔ, hty⟩
  have hZ := ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd hΔo (convex_ball _ _).isPreconnected
    hdeta hne
  obtain ⟨P, U, D, N, s, -, hUD, -, -, hnull, hfib⟩ := h₃ n d J A hJ hdim hA
  set G := Δ ∩ (fun t => (ReciprocityTheory.AnForm.A.jacC τ t).det) ⁻¹' {0}ᶜ with hGdef
  have hG : IsOpen G := hdeta.continuousOn.isOpen_inter_preimage hΔo isOpen_compl_singleton
  have hS := BranchSheetAE.volume_preimage_null hG (hτd.mono Set.inter_subset_left)
    (fun w hw => hw.2) hnull
  rw [ae_restrict_iff' hΔo.measurableSet, ae_iff]
  refine measure_mono_null ?_ (measure_union_null hZ hS)
  intro t ht
  simp only [Set.mem_ofPred_eq, Classical.not_imp] at ht
  obtain ⟨htΔ, hno⟩ := ht
  by_cases hdt : (ReciprocityTheory.AnForm.A.jacC τ t).det = 0
  · exact Or.inl ⟨htΔ, hdt⟩
  refine Or.inr ⟨⟨htΔ, hdt⟩, fun hD => hno ?_⟩
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hD
  obtain ⟨hfibk, -, hsh⟩ := hfib k (τ t) ((hUD k).2.2.1 hk)
  have hmem : γ.toFun t ∈ fibre J A (τ t) := ⟨γ.mapsTo htΔ, rfl⟩
  rw [hfibk] at hmem
  obtain ⟨j, hj⟩ := hmem
  exact ⟨s k j, hj ▸ hsh j⟩

end

end GroundTheory.Heights₂.Heights

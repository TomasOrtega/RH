import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeE
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherMore
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter

namespace pullbackBadImage_holds

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' J' : Ideal (MRing ι')} {n : ℕ}

omit [Fintype K'] in

/- English proof (translation)
Take `⟨c, hc, hzc⟩` from `R.compat z x z ⟨R.mem_U z, hz⟩`. Establish `hpt : pullPt R v z = fun p => (c ∘ κ) p.1 * R.lift x z (v p)`. Use function extensionality and compare the values at `p`. Simplify using `only [pullPt, hzc, Function.comp_apply, hv.2.2.1 p]`. Establish `hpc : ∏ k, (c ∘ κ) k ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => hc (κ k)`.

Use function extensionality and compare the values at `i`. Simplify using `only [pullQ, hpt, segre_smul, map_smul, Pi.smul_apply, smul_eq_mul]`. Conclude with `mul_div_mul_left _ _ hpc`.
-/
theorem pullQ_eq_local (hv : IsBlockMap κ v) (R : AnLogRes P' J' n)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {x z : R.X} (hz : z ∈ R.U x) :
    pullQ R v Ψ z = fun i =>
      Ψ (segre fun p => R.lift x z (v p)) i.succ / Ψ (segre fun p => R.lift x z (v p)) 0 := by
  obtain ⟨c, hc, hzc⟩ := R.compat z x z ⟨R.mem_U z, hz⟩
  have hpt : pullPt R v z = fun p => (c ∘ κ) p.1 * R.lift x z (v p) := by
    funext p
    simp only [pullPt, hzc, Function.comp_apply, hv.2.2.1 p]
  have hpc : ∏ k, (c ∘ κ) k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc (κ k)
  funext i
  simp only [pullQ, hpt, segre_smul, map_smul, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hpc

/- English proof (translation)
Use `set u := R.A.chart j x`. Establish `hsu : (R.A.chart j).symm u = x` using `(R.A.chart j).left_inv hj`. Establish `hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x` using `⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact R.mem_U x⟩`. Establish `hl` using `analyticAt_lift_chart R x j hu`. Establish `hs : AnalyticAt ℂ (fun w => segre fun p => R.lift x ((R.A.chart j).symm w) (v p)) u`.

Use `analyticAt_pi_iff.mpr fun i => ?_` and prove the remaining obligations. Simplify using `only [segre]`. Conclude with `Finset.analyticAt_fun_prod _ fun k _ => analyticAt_pi_iff.mp hl _`. Establish `hH : AnalyticAt ℂ (fun w => Ψ (segre fun p => R.lift x ((R.A.chart j).symm w) (v p))) u` using `(LinearMap.toContinuousLinearMap Ψ).analyticAt _ |>.comp hs`. Establish `hH0 : AnalyticAt ℂ (fun w => Ψ (segre fun p => R.lift x ((R.A.chart j).symm w) (v p)) 0) u` using `analyticAt_pi_iff.mp hH 0`.

Establish `hne : Ψ (segre fun p => R.lift x ((R.A.chart j).symm u) (v p)) 0 ≠ 0` using `by rw [hsu]; exact h0`. Establish `hF : AnalyticAt ℂ (fun w => fun i : Fin n => Ψ (segre fun p => R.lift x ((R.A.chart j).symm w) (v p)) i.succ / Ψ (segre fun p => R.lift x ((R.A.chart j).symm w) (v p)) 0) u` using `analyticAt_pi_iff.mpr fun i => (analyticAt_pi_iff.mp hH i.succ).div hH0 hne`. Use `hF.congr ?_` and prove the remaining obligations. Use `filter_upwards [((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds hu] with w hw`. Conclude with `(pullQ_eq_local hv R Ψ hw.2).symm`.
-/
theorem analyticAt_pullQ (hv : IsBlockMap κ v) (R : AnLogRes P' J' n)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (x : R.X) (j : Fin R.A.n)
    (hj : x ∈ (R.A.chart j).source) (h0 : Ψ (segre (pullPt R v x)) 0 ≠ 0) :
    AnalyticAt ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) := by
  classical
  set u := R.A.chart j x
  have hsu : (R.A.chart j).symm u = x := (R.A.chart j).left_inv hj
  have hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact R.mem_U x⟩
  have hl := analyticAt_lift_chart R x j hu
  have hs : AnalyticAt ℂ (fun w => segre fun p => R.lift x ((R.A.chart j).symm w) (v p)) u := by
    refine analyticAt_pi_iff.mpr fun i => ?_
    simp only [segre]
    exact Finset.analyticAt_fun_prod _ fun k _ => analyticAt_pi_iff.mp hl _
  have hH : AnalyticAt ℂ (fun w => Ψ (segre fun p => R.lift x ((R.A.chart j).symm w) (v p))) u :=
    (LinearMap.toContinuousLinearMap Ψ).analyticAt _ |>.comp hs
  have hH0 : AnalyticAt ℂ (fun w => Ψ (segre fun p => R.lift x ((R.A.chart j).symm w) (v p)) 0) u :=
    analyticAt_pi_iff.mp hH 0
  have hne : Ψ (segre fun p => R.lift x ((R.A.chart j).symm u) (v p)) 0 ≠ 0 := by rw [hsu]; exact h0
  have hF : AnalyticAt ℂ (fun w => fun i : Fin n =>
      Ψ (segre fun p => R.lift x ((R.A.chart j).symm w) (v p)) i.succ /
        Ψ (segre fun p => R.lift x ((R.A.chart j).symm w) (v p)) 0) u :=
    analyticAt_pi_iff.mpr fun i => (analyticAt_pi_iff.mp hH i.succ).div hH0 hne
  refine hF.congr ?_
  filter_upwards [((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds hu]
    with w hw
  exact (pullQ_eq_local hv R Ψ hw.2).symm

/- English proof (translation)
Take `⟨w, hw, hw0⟩` from `(Submodule.ne_bot_iff _).mp (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h)`. Use `show LinearMap.det ((f.restrictScalars ℝ : (Fin m → ℂ) →L[ℝ] (Fin m → ℂ)) : (Fin m → ℂ) →ₗ[ℝ] (Fin m → ℂ)) = 0`. Use `LinearMap.det_eq_zero_iff_ker_ne_bot.mpr ((Submodule.ne_bot_iff _).mpr ⟨w, ?_, hw0⟩)` and prove the remaining obligations. Simplify using `using hw`.
-/
theorem det_restrictScalars_eq_zero {m : ℕ} (f : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ))
    (h : LinearMap.det (f : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)) = 0) :
    (f.restrictScalars ℝ).det = 0 := by
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h)
  show LinearMap.det ((f.restrictScalars ℝ : (Fin m → ℂ) →L[ℝ] (Fin m → ℂ)) :
    (Fin m → ℂ) →ₗ[ℝ] (Fin m → ℂ)) = 0
  refine LinearMap.det_eq_zero_iff_ker_ne_bot.mpr ((Submodule.ne_bot_iff _).mpr ⟨w, ?_, hw0⟩)
  simpa using hw

end pullbackBadImage_holds

open pullbackBadImage_holds in

/- English proof (translation)
Introduce `K _ ι _ K' _ ι' _ κ v P' J' n R Ψ hv _ _ _`. Set `S₁ : Fin R.A.n → Set (Fin n → ℂ)` to `fun j => (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' ({x | R.lift x x ∈ mcPts J'} ∩ {x | Ψ (segre (pullPt R v x)) 0 ≠ 0})`. Set `S₂ : Fin R.A.n → Set (Fin n → ℂ)` to `fun j => {u | u ∈ (R.A.chart j).target ∧ Ψ (segre (pullPt R v ((R.A.chart j).symm u))) 0 ≠ 0 ∧ LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) u : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0}`. Establish `hsub : pullQ R v Ψ '' (pullBad R v Ψ ∩ {x | Ψ (segre (pullPt R v x)) 0 ≠ 0}) ⊆ ⋃ j, ((pullQ R v Ψ ∘ (R.A.chart j).symm) '' S₁ j ∪ (pullQ R v Ψ ∘ (R.A.chart j).symm) '' S₂ j)`. Introduce and unpack `_ ⟨x, ⟨hx, h0⟩, rfl⟩`.

Break down `hx with (hB | hz) | ⟨j, hj, hn⟩` into its components or cases. Take `⟨j, hj⟩` from `R.A.cover x`. Use `Set.mem_iUnion.mpr ⟨j, Or.inl ⟨R.A.chart j x, ⟨(R.A.chart j).map_source hj, ?_⟩, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Set.mem_preimage, (R.A.chart j).left_inv hj]`. Conclude with `⟨hB, h0⟩`.

Simplify using `[(R.A.chart j).left_inv hj]`. Conclude with `absurd hz h0`. Establish `hd : LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0`. Assume the negation of the conclusion as `hd`. Conclude with `hn ⟨analyticAt_pullQ hv R Ψ x j hj h0, hd⟩`.

Use `Set.mem_iUnion.mpr ⟨j, Or.inr ⟨R.A.chart j x, ⟨(R.A.chart j).map_source hj, ?_, hd⟩, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[(R.A.chart j).left_inv hj]`. Conclude with `h0`. Simplify using `[(R.A.chart j).left_inv hj]`. Use `measure_mono_null hsub (measure_iUnion_null fun j => measure_union_null ?_ ?_)` and prove the remaining obligations.

Use `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ (measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left)) (R.null j))` and prove the remaining obligations. Introduce `u hu`. Establish `hx` using `(R.A.chart j).map_target hu.1`. Establish `hcu : R.A.chart j ((R.A.chart j).symm u) = u` using `(R.A.chart j).right_inv hu.1`. Use `analyticAt_pullQ hv R Ψ _ j hx hu.2.2` as an intermediate fact.

Rewrite `this` using `[hcu]`. Conclude with `(this.differentiableAt.restrictScalars ℝ).differentiableWithinAt`. Use `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume (f' := fun u => (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) u).restrictScalars ℝ) ?_ ?_` and prove the remaining obligations. Introduce `u hu`. Establish `hx` using `(R.A.chart j).map_target hu.1`.

Establish `hcu : R.A.chart j ((R.A.chart j).symm u) = u` using `(R.A.chart j).right_inv hu.1`. Use `analyticAt_pullQ hv R Ψ _ j hx hu.2.1` as an intermediate fact. Rewrite `this` using `[hcu]`. Conclude with `(this.differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt`. Introduce `u hu`.

Conclude with `det_restrictScalars_eq_zero _ hu.2.2`.
-/
theorem pullbackBadImage_holds.proof : pullbackBadImage_holds.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' J' n R Ψ hv _ _ _
  classical
  let S₁ : Fin R.A.n → Set (Fin n → ℂ) := fun j => (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹'
    ({x | R.lift x x ∈ mcPts J'} ∩ {x | Ψ (segre (pullPt R v x)) 0 ≠ 0})
  let S₂ : Fin R.A.n → Set (Fin n → ℂ) := fun j => {u | u ∈ (R.A.chart j).target ∧
    Ψ (segre (pullPt R v ((R.A.chart j).symm u))) 0 ≠ 0 ∧
    LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) u :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0}
  have hsub : pullQ R v Ψ '' (pullBad R v Ψ ∩ {x | Ψ (segre (pullPt R v x)) 0 ≠ 0}) ⊆
      ⋃ j, ((pullQ R v Ψ ∘ (R.A.chart j).symm) '' S₁ j ∪
        (pullQ R v Ψ ∘ (R.A.chart j).symm) '' S₂ j) := by
    rintro _ ⟨x, ⟨hx, h0⟩, rfl⟩
    rcases hx with (hB | hz) | ⟨j, hj, hn⟩
    · obtain ⟨j, hj⟩ := R.A.cover x
      refine Set.mem_iUnion.mpr ⟨j, Or.inl ⟨R.A.chart j x, ⟨(R.A.chart j).map_source hj, ?_⟩, ?_⟩⟩
      · rw [Set.mem_preimage, (R.A.chart j).left_inv hj]; exact ⟨hB, h0⟩
      · simp [(R.A.chart j).left_inv hj]
    · exact absurd hz h0
    · have hd : LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
          (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0 := by
        by_contra hd
        exact hn ⟨analyticAt_pullQ hv R Ψ x j hj h0, hd⟩
      refine Set.mem_iUnion.mpr ⟨j, Or.inr ⟨R.A.chart j x, ⟨(R.A.chart j).map_source hj, ?_, hd⟩, ?_⟩⟩
      · rw [(R.A.chart j).left_inv hj]; exact h0
      · simp [(R.A.chart j).left_inv hj]
  refine measure_mono_null hsub (measure_iUnion_null fun j => measure_union_null ?_ ?_)
  · refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
      (measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left))
        (R.null j))
    intro u hu
    have hx := (R.A.chart j).map_target hu.1
    have hcu : R.A.chart j ((R.A.chart j).symm u) = u := (R.A.chart j).right_inv hu.1
    have := analyticAt_pullQ hv R Ψ _ j hx hu.2.2
    rw [hcu] at this
    exact (this.differentiableAt.restrictScalars ℝ).differentiableWithinAt
  · refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun u => (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) u).restrictScalars ℝ) ?_ ?_
    · intro u hu
      have hx := (R.A.chart j).map_target hu.1
      have hcu : R.A.chart j ((R.A.chart j).symm u) = u := (R.A.chart j).right_inv hu.1
      have := analyticAt_pullQ hv R Ψ _ j hx hu.2.1
      rw [hcu] at this
      exact (this.differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    · intro u hu
      exact det_restrictScalars_eq_zero _ hu.2.2

end GroundTheory.Heights₂.Heights.Inter

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeD
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgeProj
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge

open ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}
  (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

/- English proof (translation)
The claim follows from `analyticAt_pi_iff.mpr fun p => R.holo x p j u hu`.
-/
theorem analyticAt_lift_chart (x : R.X) (j : Fin R.A.n) {u : Fin e → ℂ}
    (hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) :
    AnalyticAt ℂ (fun v => R.lift x ((R.A.chart j).symm v)) u :=
  analyticAt_pi_iff.mpr fun p => R.holo x p j u hu

/- English proof (translation)
Take `⟨c, hc, hzc⟩` from `R.compat z x z ⟨R.mem_U z, hz⟩`. Establish `hpc : ∏ k, c k ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => hc k`. Use function extensionality and compare the values at `i`. Simplify using `only [brQ, hzc, segre_smul, map_smul, Pi.smul_apply, smul_eq_mul]`. Conclude with `mul_div_mul_left _ _ hpc`.
-/
theorem brQ_eq_local {x z : R.X} (hz : z ∈ R.U x) :
    brQ R Ψ z = fun i => Ψ (segre (R.lift x z)) i.succ / Ψ (segre (R.lift x z)) 0 := by
  obtain ⟨c, hc, hzc⟩ := R.compat z x z ⟨R.mem_U z, hz⟩
  have hpc : ∏ k, c k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  funext i
  simp only [brQ, hzc, segre_smul, map_smul, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hpc

/- English proof (translation)
Establish `hl` using `analyticAt_lift_chart R x j hu`. Establish `hs : AnalyticAt ℂ (fun v => segre (R.lift x ((R.A.chart j).symm v))) u`. Use `analyticAt_pi_iff.mpr fun i => ?_` and prove the remaining obligations. Simplify using `only [segre]`. Conclude with `Finset.analyticAt_fun_prod _ fun k _ => analyticAt_pi_iff.mp hl _`.

Conclude with `(LinearMap.toContinuousLinearMap Ψ).analyticAt _ |>.comp hs`.
-/
theorem analyticAt_segre_lift (x : R.X) (j : Fin R.A.n) {u : Fin e → ℂ}
    (hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) :
    AnalyticAt ℂ (fun v => Ψ (segre (R.lift x ((R.A.chart j).symm v)))) u := by
  classical
  have hl := analyticAt_lift_chart R x j hu
  have hs : AnalyticAt ℂ (fun v => segre (R.lift x ((R.A.chart j).symm v))) u := by
    refine analyticAt_pi_iff.mpr fun i => ?_
    simp only [segre]
    exact Finset.analyticAt_fun_prod _ fun k _ => analyticAt_pi_iff.mp hl _
  exact (LinearMap.toContinuousLinearMap Ψ).analyticAt _ |>.comp hs

/- English proof (translation)
Use `set u := R.A.chart j x`. Establish `hsu : (R.A.chart j).symm u = x` using `(R.A.chart j).left_inv hj`. Establish `hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x` using `⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact R.mem_U x⟩`. Establish `hH` using `analyticAt_segre_lift R Ψ x j hu`. Establish `hH0 : AnalyticAt ℂ (fun v => Ψ (segre (R.lift x ((R.A.chart j).symm v))) 0) u` using `analyticAt_pi_iff.mp hH 0`.

Establish `hne : Ψ (segre (R.lift x ((R.A.chart j).symm u))) 0 ≠ 0` using `by rw [hsu]; exact h0`. Establish `hF : AnalyticAt ℂ (fun v => fun i : Fin e => Ψ (segre (R.lift x ((R.A.chart j).symm v))) i.succ / Ψ (segre (R.lift x ((R.A.chart j).symm v))) 0) u` using `analyticAt_pi_iff.mpr fun i => (analyticAt_pi_iff.mp hH i.succ).div hH0 hne`. Use `hF.congr ?_` and prove the remaining obligations. Use `filter_upwards [((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds hu, hH0.continuousAt.eventually_ne hne] with v hv hv0`. Conclude with `(brQ_eq_local R Ψ hv.2).symm`.
-/
theorem analyticAt_brQ (x : R.X) (j : Fin R.A.n) (hj : x ∈ (R.A.chart j).source)
    (h0 : Ψ (segre (R.lift x x)) 0 ≠ 0) :
    AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) := by
  set u := R.A.chart j x
  have hsu : (R.A.chart j).symm u = x := (R.A.chart j).left_inv hj
  have hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact R.mem_U x⟩
  have hH := analyticAt_segre_lift R Ψ x j hu
  have hH0 : AnalyticAt ℂ (fun v => Ψ (segre (R.lift x ((R.A.chart j).symm v))) 0) u :=
    analyticAt_pi_iff.mp hH 0
  have hne : Ψ (segre (R.lift x ((R.A.chart j).symm u))) 0 ≠ 0 := by rw [hsu]; exact h0
  have hF : AnalyticAt ℂ (fun v => fun i : Fin e =>
      Ψ (segre (R.lift x ((R.A.chart j).symm v))) i.succ /
        Ψ (segre (R.lift x ((R.A.chart j).symm v))) 0) u :=
    analyticAt_pi_iff.mpr fun i => (analyticAt_pi_iff.mp hH i.succ).div hH0 hne
  refine hF.congr ?_
  filter_upwards [((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds hu,
    hH0.continuousAt.eventually_ne hne] with v hv hv0
  exact (brQ_eq_local R Ψ hv.2).symm

/- English proof (translation)
Use `set T := brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0}`. Establish `hsub : brQ R Ψ '' T ⊆ ⋃ j, (brQ R Ψ ∘ (R.A.chart j).symm) '' ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' T)`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨j, hj⟩` from `R.A.cover x`. Use `Set.mem_iUnion.mpr ⟨j, R.A.chart j x, ⟨(R.A.chart j).map_source hj, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Set.mem_preimage, (R.A.chart j).left_inv hj]`. Conclude with `hx`. Simplify using `[(R.A.chart j).left_inv hj]`. Use `measure_mono_null hsub (measure_iUnion_null fun j => ?_)` and prove the remaining obligations. Use `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ (measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left)) (hS j))` and prove the remaining obligations.

Introduce `u hu`. Establish `hx` using `(R.A.chart j).map_target hu.1`. Establish `hcu : R.A.chart j ((R.A.chart j).symm u) = u` using `(R.A.chart j).right_inv hu.1`. Use `analyticAt_brQ R Ψ _ j hx hu.2.2` as an intermediate fact. Rewrite `this` using `[hcu]`.

Conclude with `(this.differentiableAt.restrictScalars ℝ).differentiableWithinAt`.
-/
theorem brQ_image_null_of
    (hS : ∀ j, volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' brBad R Ψ) = 0) :
    volume (brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) = 0 := by
  set T := brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0}
  have hsub : brQ R Ψ '' T ⊆ ⋃ j, (brQ R Ψ ∘ (R.A.chart j).symm) ''
      ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' T) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, hj⟩ := R.A.cover x
    refine Set.mem_iUnion.mpr ⟨j, R.A.chart j x, ⟨(R.A.chart j).map_source hj, ?_⟩, ?_⟩
    · rw [Set.mem_preimage, (R.A.chart j).left_inv hj]; exact hx
    · simp [(R.A.chart j).left_inv hj]
  refine measure_mono_null hsub (measure_iUnion_null fun j => ?_)
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
    (measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left))
      (hS j))
  intro u hu
  have hx := (R.A.chart j).map_target hu.1
  have hcu : R.A.chart j ((R.A.chart j).symm u) = u := (R.A.chart j).right_inv hu.1
  have := analyticAt_brQ R Ψ _ j hx hu.2.2
  rw [hcu] at this
  exact (this.differentiableAt.restrictScalars ℝ).differentiableWithinAt

end GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge

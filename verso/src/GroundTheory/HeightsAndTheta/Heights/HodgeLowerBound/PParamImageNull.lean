import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsParamImageNull
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[segre, torusSmul, Finset.prod_mul_distrib]`.
-/
theorem ParamImageNull.segre_torusSmul {K : Type} [Fintype K] {ι : K → Type} (c : K → ℂ) (v : (Σ k, ι k) → ℂ) :
    segre (torusSmul c v) = (∏ k, c k) • segre v := by
  funext x
  simp [segre, torusSmul, Finset.prod_mul_distrib]

/- English proof (translation)
Use `differentiableAt_pi.2 fun x => ?_` and prove the remaining obligations. Simplify using `only [segre]`. Establish `hk : ∀ k, DifferentiableAt ℂ (fun u => f u ⟨k, x k⟩) w` using `fun k => differentiableAt_pi.1 hf ⟨k, x k⟩`. Use `fun_prop`.
-/
theorem ParamImageNull.differentiableAt_segre_comp {K : Type} [Fintype K] {ι : K → Type} {d : ℕ}
    {f : (Fin d → ℂ) → (Σ k, ι k) → ℂ} {w : Fin d → ℂ} (hf : DifferentiableAt ℂ f w) :
    DifferentiableAt ℂ (fun u => segre (f u)) w := by
  refine differentiableAt_pi.2 fun x => ?_
  simp only [segre]
  have hk : ∀ k, DifferentiableAt ℂ (fun u => f u ⟨k, x k⟩) w := fun k => differentiableAt_pi.1 hf ⟨k, x k⟩
  fun_prop

/- English proof (translation)
Introduce `K _ ι _ P d m V A γ N _hV hAV hA hγ hN Ψ _`. Use `set G : Fin m → (Fin d → ℂ) → Fin (d + 1) → ℂ := fun i w => Ψ (segre (γ i w)) with hG`. Use `set F : Fin m → (Fin d → ℂ) → Fin d → ℂ := fun i w l => G i w l.succ / G i w 0 with hF`. Establish `hsub : {y : Fin d → ℂ | ∃ z ∈ mcPts P, z ∈ N ∧ Ψ (segre z) = Fin.cons 1 y} ⊆ ⋃ i, F i '' (A i ∩ {w | G i w 0 ≠ 0})`. Introduce and unpack `y ⟨z, hzP, hzN, hzy⟩`.

Take `⟨i, w, hw, c, hc, rfl⟩` from `hN z ⟨hzN, hzP⟩`. Rewrite `hzy` using `[ParamImageNull.segre_torusSmul, map_smul]`. Establish `h0` using `congrFun hzy 0`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero] at h0`. Establish `hG0 : G i w 0 ≠ 0`.

Introduce `h`. Rewrite `h` using `[hG]`. Simplify using `only at h`. Rewrite `h0` using `[h, mul_zero]`. Conclude with `zero_ne_one h0`.

Use `Set.mem_iUnion.2 ⟨i, w, ⟨hw, hG0⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `l`. Establish `hl` using `congrFun hzy l.succ`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ] at hl`. Simplify using `only [hF]`.

Rewrite using `[div_eq_iff hG0, ← hl]`. Establish `h0' : (∏ k, c k) * G i w 0 = 1` using `h0`. Combine the equalities or inequalities in the displayed calculation. Use `measure_mono_null hsub (measure_iUnion_null fun i => ?_)` and prove the remaining obligations. Use `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ (measure_mono_null Set.inter_subset_left (hA i))` and prove the remaining obligations.

Introduce `w ⟨hwA, hw0⟩`. Establish `hγw : DifferentiableAt ℂ (γ i) w` using `(hγ i w (hAV i hwA)).differentiableAt`. Establish `hGw : DifferentiableAt ℂ (G i) w` using `(LinearMap.toContinuousLinearMap Ψ).differentiableAt.comp w (ParamImageNull.differentiableAt_segre_comp hγw)`. Establish `hFw : DifferentiableAt ℂ (F i) w`. Use `differentiableAt_pi.2 fun l => ?_` and prove the remaining obligations.

Use `show DifferentiableAt ℂ (fun u => G i u l.succ / G i u 0) w`. Simplify using `only [div_eq_mul_inv]`. Conclude with `(differentiableAt_pi.1 hGw l.succ).mul ((differentiableAt_pi.1 hGw 0).inv hw0)`. Conclude with `(hFw.restrictScalars ℝ).differentiableWithinAt`.
-/
theorem ParamImageNull.proof : ParamImageNull.Statement := by
  intro K _ ι _ P d m V A γ N _hV hAV hA hγ hN Ψ _
  classical
  set G : Fin m → (Fin d → ℂ) → Fin (d + 1) → ℂ := fun i w => Ψ (segre (γ i w)) with hG
  set F : Fin m → (Fin d → ℂ) → Fin d → ℂ := fun i w l => G i w l.succ / G i w 0 with hF
  have hsub : {y : Fin d → ℂ | ∃ z ∈ mcPts P, z ∈ N ∧ Ψ (segre z) = Fin.cons 1 y} ⊆
      ⋃ i, F i '' (A i ∩ {w | G i w 0 ≠ 0}) := by
    rintro y ⟨z, hzP, hzN, hzy⟩
    obtain ⟨i, w, hw, c, hc, rfl⟩ := hN z ⟨hzN, hzP⟩
    rw [ParamImageNull.segre_torusSmul, map_smul] at hzy
    have h0 := congrFun hzy 0
    simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero] at h0
    have hG0 : G i w 0 ≠ 0 := by
      intro h
      rw [hG] at h
      simp only at h
      rw [h, mul_zero] at h0
      exact zero_ne_one h0
    refine Set.mem_iUnion.2 ⟨i, w, ⟨hw, hG0⟩, ?_⟩
    funext l
    have hl := congrFun hzy l.succ
    simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ] at hl
    simp only [hF]
    rw [div_eq_iff hG0, ← hl]
    have h0' : (∏ k, c k) * G i w 0 = 1 := h0
    calc G i w l.succ = G i w l.succ * ((∏ k, c k) * G i w 0) := by rw [h0', mul_one]
      _ = (∏ k, c k) * Ψ (segre (γ i w)) l.succ * G i w 0 := by simp only [hG]; ring
  refine measure_mono_null hsub (measure_iUnion_null fun i => ?_)
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
    (measure_mono_null Set.inter_subset_left (hA i))
  intro w ⟨hwA, hw0⟩
  have hγw : DifferentiableAt ℂ (γ i) w := (hγ i w (hAV i hwA)).differentiableAt
  have hGw : DifferentiableAt ℂ (G i) w :=
    (LinearMap.toContinuousLinearMap Ψ).differentiableAt.comp w (ParamImageNull.differentiableAt_segre_comp hγw)
  have hFw : DifferentiableAt ℂ (F i) w := by
    refine differentiableAt_pi.2 fun l => ?_
    show DifferentiableAt ℂ (fun u => G i u l.succ / G i u 0) w
    simp only [div_eq_mul_inv]
    exact (differentiableAt_pi.1 hGw l.succ).mul ((differentiableAt_pi.1 hGw 0).inv hw0)
  exact (hFw.restrictScalars ℝ).differentiableWithinAt

end GroundTheory.Heights₂.Heights.LowerBoundFree

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPtsMonoSemipos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntegralAgainstPositive
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

/- English proof (translation)
Establish `hA : AnalyticAt ℂ γ y` using `sheet_analyticAt osgood h`. Establish `hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P` using `h.2.mono fun _ hy' => hy'.2.1`. Establish `hy : γ y ∈ mcPts P` using `hpts.self_of_nhds`. Establish `hh : ContDiffAt ℝ 2 L.h (γ y)` using `(hsp.1.contDiffAt (HilbertSamuel.IntegralAgainstPositive.isOpen_blocksNonzero.mem_nhds hy.1)).of_le (WithTop.coe_le_coe.2 le_top)`. Establish `hlog : ContDiffAt ℝ 2 (fun z => Real.log (L.h z)) (γ y)` using `hh.log (L.pos _ hy.1).ne'`.

Establish `h2 : ContDiffAt ℝ 2 (fun y' => Real.log (L.h (γ y'))) y` using `hlog.comp y (hA.contDiffAt.restrict_scalars ℝ)`. Establish `h2r : ContDiffAt ℝ 2 (fun y' => Real.log (L.h (γ y')) / r) y` using `h2.div_const r`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_maDensity_eq_maDens]`. Use `ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun _ => ?_` and prove the remaining obligations. Use `ReciprocityTheory.AnForm.A.hessC_posSemidef_of_levi _ _ h2r fun ξ => ?_` and prove the remaining obligations.

Establish `hfun : (fun y' => Real.log (L.h (γ y')) / r) = fun y' => (fun _ : Fin e → ℂ => (0 : ℝ)) y' + r⁻¹ * Real.log (L.h (γ y'))`. Use function extensionality and compare the values at `y'`. Simplify using `[div_eq_inv_mul]`. Rewrite using `[hfun, ReciprocityTheory.AnForm.levi_add_smul r⁻¹ contDiffAt_const h2 ξ]`. Establish `h0 : ReciprocityTheory.AnForm.levi (fun _ : Fin e → ℂ => (0 : ℝ)) y ξ = 0`.

Simplify using `[ReciprocityTheory.AnForm.levi]`. Establish `hc : 0 ≤ ReciprocityTheory.AnForm.levi ((fun z => Real.log (L.h z)) ∘ γ) y ξ`. Rewrite using `[ReciprocityTheory.AnForm.levi_comp (φ := fun z => Real.log (L.h z)) ξ hA hlog]`. Conclude with `hsp.2 _ hy _ (HilbertSamuel.IntegralAgainstPositive.isConeTangent_of_sheet le_rfl hA hpts ξ)`. Rewrite using `[h0, zero_add]`.

Conclude with `mul_nonneg (inv_nonneg.2 hr.le) hc`.
-/
theorem maDensity_logDiv_nonneg_of_sheet {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {L : HermLine ι} (hsp : IsSemipositiveH P L) {r : ℝ} (hr : 0 < r) {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} (h : IsSheet P Ψ y w γ) :
    0 ≤ maDensity (fun (_ : Fin e) y' => Real.log (L.h (γ y')) / r) y := by
  have hA : AnalyticAt ℂ γ y := sheet_analyticAt osgood h
  have hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P := h.2.mono fun _ hy' => hy'.2.1
  have hy : γ y ∈ mcPts P := hpts.self_of_nhds
  have hh : ContDiffAt ℝ 2 L.h (γ y) :=
    (hsp.1.contDiffAt
      (HilbertSamuel.IntegralAgainstPositive.isOpen_blocksNonzero.mem_nhds hy.1)).of_le
      (WithTop.coe_le_coe.2 le_top)
  have hlog : ContDiffAt ℝ 2 (fun z => Real.log (L.h z)) (γ y) := hh.log (L.pos _ hy.1).ne'
  have h2 : ContDiffAt ℝ 2 (fun y' => Real.log (L.h (γ y'))) y :=
    hlog.comp y (hA.contDiffAt.restrict_scalars ℝ)
  have h2r : ContDiffAt ℝ 2 (fun y' => Real.log (L.h (γ y')) / r) y := h2.div_const r
  rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_maDensity_eq_maDens]
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun _ => ?_
  refine ReciprocityTheory.AnForm.A.hessC_posSemidef_of_levi _ _ h2r fun ξ => ?_
  have hfun : (fun y' => Real.log (L.h (γ y')) / r) =
      fun y' => (fun _ : Fin e → ℂ => (0 : ℝ)) y' + r⁻¹ * Real.log (L.h (γ y')) := by
    funext y'
    simp [div_eq_inv_mul]
  rw [hfun, ReciprocityTheory.AnForm.levi_add_smul r⁻¹ contDiffAt_const h2 ξ]
  have h0 : ReciprocityTheory.AnForm.levi (fun _ : Fin e → ℂ => (0 : ℝ)) y ξ = 0 := by
    simp [ReciprocityTheory.AnForm.levi]
  have hc : 0 ≤ ReciprocityTheory.AnForm.levi ((fun z => Real.log (L.h z)) ∘ γ) y ξ := by
    rw [ReciprocityTheory.AnForm.levi_comp (φ := fun z => Real.log (L.h z)) ξ hA hlog]
    exact hsp.2 _ hy _ (HilbertSamuel.IntegralAgainstPositive.isConeTangent_of_sheet le_rfl hA hpts ξ)
  rw [h0, zero_add]
  exact mul_nonneg (inv_nonneg.2 hr.le) hc

/- English proof (translation)
Introduce `K _ ι _ P e L r g₁ g₂ N hP hL hr hN hle h1 h2`. Unfold `ptsIntegral`. Distinguish the cases in `hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ`. Use `swap`. Rewrite using `[dif_neg hΨ, dif_neg hΨ]`.

Rewrite using `[dif_pos hΨ, dif_pos hΨ]`. Establish `hΨg : IsGoodProj P hΨ.choose` using `hΨ.choose_spec`. Unfold `ptsIntegralAt`. Use `integral_mono_ae (h1 _ hΨg) (h2 _ hΨg) ?_` and prove the remaining obligations. Rewrite using `[Filter.EventuallyLE, ae_iff]`.

Use `measure_mono_null (fun y hy => ?_) (hN _ hΨg)` and prove the remaining obligations. Assume the negation of the conclusion as `hyB`. Apply `hy` to reduce the goal to its premises. Establish `hfin` using `fibreFinite K ι P e hΨ.choose hP hΨg y`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]`.

Use `Finset.sum_le_sum fun w _ => ?_` and prove the remaining obligations. Unfold `sheetDensity`. Distinguish the cases in `hγ : ∃ γ, IsSheet P hΨ.choose y w γ`. Rewrite using `[dif_pos hγ, dif_pos hγ]`. Take `⟨-, hev⟩` from `hγ.choose_spec`.

Take `⟨-, hmem, hproj⟩` from `hev.self_of_nhds`. Establish `hnot : hγ.choose y ∉ N` using `fun hN' => hyB ⟨hγ.choose y, hmem, hN', hproj⟩`. Conclude with `mul_le_mul_of_nonneg_right (hle _ hmem hnot) (maDensity_logDiv_nonneg_of_sheet hL hr hγ.choose_spec)`. Rewrite using `[dif_neg hγ, dif_neg hγ]`.
-/
theorem PtsMonoSemipos.proof : PtsMonoSemipos.Statement := by
  intro K _ ι _ P e L r g₁ g₂ N hP hL hr hN hle h1 h2
  classical
  unfold ptsIntegral
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ
  swap
  · rw [dif_neg hΨ, dif_neg hΨ]
  rw [dif_pos hΨ, dif_pos hΨ]
  have hΨg : IsGoodProj P hΨ.choose := hΨ.choose_spec
  unfold ptsIntegralAt
  refine integral_mono_ae (h1 _ hΨg) (h2 _ hΨg) ?_
  rw [Filter.EventuallyLE, ae_iff]
  refine measure_mono_null (fun y hy => ?_) (hN _ hΨg)
  by_contra hyB
  apply hy
  have hfin := fibreFinite K ι P e hΨ.choose hP hΨg y
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine Finset.sum_le_sum fun w _ => ?_
  unfold sheetDensity
  by_cases hγ : ∃ γ, IsSheet P hΨ.choose y w γ
  · rw [dif_pos hγ, dif_pos hγ]
    obtain ⟨-, hev⟩ := hγ.choose_spec
    obtain ⟨-, hmem, hproj⟩ := hev.self_of_nhds
    have hnot : hγ.choose y ∉ N := fun hN' => hyB ⟨hγ.choose y, hmem, hN', hproj⟩
    exact mul_le_mul_of_nonneg_right (hle _ hmem hnot)
      (maDensity_logDiv_nonneg_of_sheet hL hr hγ.choose_spec)
  · rw [dif_neg hγ, dif_neg hγ]

end GroundTheory.Heights₂.Heights.LowerBoundFree

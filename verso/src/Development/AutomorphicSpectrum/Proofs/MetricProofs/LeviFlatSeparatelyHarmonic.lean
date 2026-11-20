import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric

/- English proof (translation)
Introduce `n φ O hO hφ hl z hz i`. Use `set e : Fin n → ℂ := Pi.single i 1 with he`. Set `L : ℂ →L[ℝ] (Fin n → ℂ)` to `((ContinuousLinearMap.id ℂ ℂ).smulRight e).restrictScalars ℝ`. Establish `hLw : ∀ w : ℂ, L w = w • e` using `fun _ => rfl`. Use `set z0 : Fin n → ℂ := Function.update z i 0 with hz0`.

Establish `hupd : ∀ t : ℂ, Function.update z i t = z0 + t • e`. Introduce `t`. Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality.

Simplify using `[hz0, he]`. Simplify using `[hz0, he, h]`. Establish `hline : ∀ t : ℂ, HasFDerivAt (fun w : ℂ => z0 + w • e) L t` using `fun t => L.hasFDerivAt.const_add z0`. Establish `hcont : Continuous (fun t : ℂ => z0 + t • e)` using `by fun_prop`. Establish `hU : IsOpen ((fun t : ℂ => z0 + t • e) ⁻¹' O)` using `hO.preimage hcont`.

Establish `hzU : z i ∈ (fun t : ℂ => z0 + t • e) ⁻¹' O` using `by show z0 + z i • e ∈ O`. Rewrite using `[← hupd]`. Simplify using `using hz`. Apply the tactic sequence `have hφ2 : ∀ y ∈ O, ContDiffAt ℝ 2 φ y := fun y hy => ((hφ y hy).contDiffAt (hO.mem_nhds hy)).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | simp)`. Establish `hlap : ∀ t ∈ (fun t : ℂ => z0 + t • e) ⁻¹' O, Laplacian.laplacian (fun t : ℂ => φ (z0 + t • e)) t = 0`.

Introduce `t ht`. Establish `hy : z0 + t • e ∈ O` using `ht`. Establish `h1 : fderiv ℝ (fun w : ℂ => φ (z0 + w • e)) =ᶠ[𝓝 t] fun w : ℂ => (fderiv ℝ φ (z0 + w • e)).comp L` using `by filter_upwards [hU.mem_nhds ht] with w hw`. Conclude with `(((hφ2 _ hw).differentiableAt (by simp)).hasFDerivAt.comp w (hline w)).fderiv`. Establish `hD : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) (z0 + t • e)) (z0 + t • e)` using `(((hφ2 _ hy).fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt`.

Establish `h2` using `((hD.comp t (hline t)).clm_comp (hasFDerivAt_const L t)).fderiv`. Simplify using `only [Function.comp_def] at h2`. Establish `hle` using `hl _ hy e`. Unfold `levi at hle`. Rewrite using `[InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]`.

Simplify using `only [iteratedFDeriv_two_apply]`. Rewrite using `[h1.fderiv_eq, h2]`. Simplify using `[hLw]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[show (fun t : ℂ => φ (Function.update z i t)) = fun t : ℂ => φ (z0 + t • e) from`.

Use function extensionality and compare the values at `fun t => by rw [hupd]]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hA : ContDiffAt ℝ 2 (fun t : ℂ => z0 + t • e) (z i)`. Establish `: ContDiff ℝ 2 (fun t : ℂ => z0 + L t)` using `contDiff_const.add L.contDiff`. Conclude with `this.contDiffAt`.

Conclude with `(hφ2 _ hzU).comp (z i) hA`. Use `filter_upwards [hU.mem_nhds hzU] with t ht`. Simplify using `using hlap t ht`.
-/
theorem harmonicAt_update_of_levi_eq_zero :
    ∀ (n : ℕ) (φ : (Fin n → ℂ) → ℝ) (O : Set (Fin n → ℂ)), IsOpen O → ContDiffOn ℝ ∞ φ O →
      (∀ z ∈ O, ∀ w, levi φ z w = 0) → ∀ z ∈ O, ∀ i,
        InnerProductSpace.HarmonicAt (fun t : ℂ => φ (Function.update z i t)) (z i) := by
  intro n φ O hO hφ hl z hz i
  set e : Fin n → ℂ := Pi.single i 1 with he
  let L : ℂ →L[ℝ] (Fin n → ℂ) := ((ContinuousLinearMap.id ℂ ℂ).smulRight e).restrictScalars ℝ
  have hLw : ∀ w : ℂ, L w = w • e := fun _ => rfl
  set z0 : Fin n → ℂ := Function.update z i 0 with hz0
  have hupd : ∀ t : ℂ, Function.update z i t = z0 + t • e := by
    intro t
    funext j
    by_cases h : j = i
    · subst h
      simp [hz0, he]
    · simp [hz0, he, h]
  have hline : ∀ t : ℂ, HasFDerivAt (fun w : ℂ => z0 + w • e) L t := fun t =>
    L.hasFDerivAt.const_add z0
  have hcont : Continuous (fun t : ℂ => z0 + t • e) := by fun_prop
  have hU : IsOpen ((fun t : ℂ => z0 + t • e) ⁻¹' O) := hO.preimage hcont
  have hzU : z i ∈ (fun t : ℂ => z0 + t • e) ⁻¹' O := by
    show z0 + z i • e ∈ O
    rw [← hupd]
    simpa using hz
  have hφ2 : ∀ y ∈ O, ContDiffAt ℝ 2 φ y := fun y hy =>
    ((hφ y hy).contDiffAt (hO.mem_nhds hy)).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | simp)
  have hlap : ∀ t ∈ (fun t : ℂ => z0 + t • e) ⁻¹' O,
      Laplacian.laplacian (fun t : ℂ => φ (z0 + t • e)) t = 0 := by
    intro t ht
    have hy : z0 + t • e ∈ O := ht
    have h1 : fderiv ℝ (fun w : ℂ => φ (z0 + w • e)) =ᶠ[𝓝 t]
        fun w : ℂ => (fderiv ℝ φ (z0 + w • e)).comp L := by
      filter_upwards [hU.mem_nhds ht] with w hw
      exact (((hφ2 _ hw).differentiableAt (by simp)).hasFDerivAt.comp w (hline w)).fderiv
    have hD : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) (z0 + t • e)) (z0 + t • e) :=
      (((hφ2 _ hy).fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt
    have h2 := ((hD.comp t (hline t)).clm_comp (hasFDerivAt_const L t)).fderiv
    simp only [Function.comp_def] at h2
    have hle := hl _ hy e
    unfold levi at hle
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
    simp only [iteratedFDeriv_two_apply]
    rw [h1.fderiv_eq, h2]
    simp [hLw]
    linarith
  rw [show (fun t : ℂ => φ (Function.update z i t)) = fun t : ℂ => φ (z0 + t • e) from
    funext fun t => by rw [hupd]]
  refine ⟨?_, ?_⟩
  · have hA : ContDiffAt ℝ 2 (fun t : ℂ => z0 + t • e) (z i) := by
      have : ContDiff ℝ 2 (fun t : ℂ => z0 + L t) := contDiff_const.add L.contDiff
      exact this.contDiffAt
    exact (hφ2 _ hzU).comp (z i) hA
  · filter_upwards [hU.mem_nhds hzU] with t ht
    simpa using hlap t ht

end GlobalTheory.CompanionTheory.Metric

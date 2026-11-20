import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHermExtend
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open Filter Topology Metric
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.AnForm (levi levi_comp levi_congr levi_add_smul levi_re_analytic)

namespace LevelTowerAlt

/- English proof (translation)
Substitute `h0` using the available equality. Establish `hτ : AnalyticAt ℂ (fun s : Fin 1 → ℂ => δ (s 0)) 0` using `AnalyticAt.comp (g := δ) (f := fun s : Fin 1 → ℂ => s 0) hδ ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt 0)`. Establish `h` using `HasFDerivAt.comp (0 : Fin 1 → ℂ) (g := δ) (f := fun s : Fin 1 → ℂ => s 0) hd.hasFDerivAt (hasFDerivAt_apply 0 0)`. Establish `h2 : fderiv ℂ (fun s : Fin 1 → ℂ => δ (s 0)) 0 (fun _ => 1) = w`. Rewrite using `[show fderiv ℂ (fun s : Fin 1 → ℂ => δ (s 0)) 0 = _ from h.fderiv]`.

Simplify using the standard rewrite rules. Establish `h3` using `levi_comp (φ := φ) (τ := fun s : Fin 1 → ℂ => δ (s 0)) (z := 0) (fun _ => 1) hτ hφ`. Rewrite `h3` using `[h2]`. Conclude with `h3.symm`.
-/
theorem levi_disc {ι : Type} [Fintype ι] {φ : (ι → ℂ) → ℝ} {δ : ℂ → ι → ℂ} {z w : ι → ℂ} (hδ : AnalyticAt ℂ δ 0)
    (hd : HasDerivAt δ w 0) (h0 : δ 0 = z) (hφ : ContDiffAt ℝ 2 φ z) :
    levi φ z w = levi (fun s : Fin 1 → ℂ => φ (δ (s 0))) 0 (fun _ => 1) := by
  subst h0
  have hτ : AnalyticAt ℂ (fun s : Fin 1 → ℂ => δ (s 0)) 0 :=
    AnalyticAt.comp (g := δ) (f := fun s : Fin 1 → ℂ => s 0) hδ
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt 0)
  have h := HasFDerivAt.comp (0 : Fin 1 → ℂ) (g := δ) (f := fun s : Fin 1 → ℂ => s 0) hd.hasFDerivAt
    (hasFDerivAt_apply 0 0)
  have h2 : fderiv ℂ (fun s : Fin 1 → ℂ => δ (s 0)) 0 (fun _ => 1) = w := by
    rw [show fderiv ℂ (fun s : Fin 1 → ℂ => δ (s 0)) 0 = _ from h.fderiv]
    simp
  have h3 := levi_comp (φ := φ) (τ := fun s : Fin 1 → ℂ => δ (s 0)) (z := 0) (fun _ => 1) hτ hφ
  rw [h2] at h3
  exact h3.symm

/- English proof (translation)
Establish `hR : AnalyticAt ℝ G z` using `hG.restrictScalars`. Establish `hre : ContDiffAt ℝ 2 (fun y => (G y).re) z` using `Complex.reCLM.contDiff.contDiffAt.comp z hR.contDiffAt`. Establish `h' : f =ᶠ[𝓝 z] fun y => g y + 1 * (G y).re` using `h.mono fun y hy => by simp only [hy, one_mul]`. Rewrite using `[levi_congr h', levi_add_smul 1 hg hre, levi_re_analytic hG, mul_zero, add_zero]`.
-/
theorem levi_add_re {ι : Type} [Fintype ι] {f g : (ι → ℂ) → ℝ} {G : (ι → ℂ) → ℂ} {z : ι → ℂ}
    (hg : ContDiffAt ℝ 2 g z) (hG : AnalyticAt ℂ G z) (h : ∀ᶠ y in 𝓝 z, f y = g y + (G y).re) (w : ι → ℂ) :
    levi f z w = levi g z w := by
  have hR : AnalyticAt ℝ G z := hG.restrictScalars
  have hre : ContDiffAt ℝ 2 (fun y => (G y).re) z := Complex.reCLM.contDiff.contDiffAt.comp z hR.contDiffAt
  have h' : f =ᶠ[𝓝 z] fun y => g y + 1 * (G y).re := h.mono fun y hy => by simp only [hy, one_mul]
  rw [levi_congr h', levi_add_smul 1 hg hre, levi_re_analytic hG, mul_zero, add_zero]

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

/- English proof (translation)
Establish `hp : ∀ k, ‖c k‖ ^ A.a k ≠ 0` using `fun k => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))`. Express the relevant statement in the definitionally equal form `Real.log (A.h fun p => c p.1 * z p) = _`. Rewrite using `[A.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => hp k) (A.pos z hz).ne', Real.log_prod fun k _ => hp k, add_comm]`. Simplify using `only [Real.log_zpow]`.
-/
theorem log_h_smul (A : HermLine J) {z : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) {c : K → ℂ}
    (hc : ∀ k, c k ≠ 0) :
    Real.log (A.h (torusSmul c z)) = Real.log (A.h z) + ∑ k, (A.a k : ℝ) * Real.log ‖c k‖ := by
  have hp : ∀ k, ‖c k‖ ^ A.a k ≠ 0 := fun k => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  change Real.log (A.h fun p => c p.1 * z p) = _
  rw [A.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => hp k) (A.pos z hz).ne',
    Real.log_prod fun k _ => hp k, add_comm]
  simp only [Real.log_zpow]

/- English proof (translation)
The claim follows from `((ContDiffOn.contDiffAt hA (HermExtend.isOpen_blocksNe.mem_nhds hz)).log (A.pos z hz).ne').of_le (WithTop.coe_le_coe.2 le_top)`.
-/
theorem contDiffAt_log_h {A : HermLine J} (hA : IsSmoothHerm A) {z : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ContDiffAt ℝ 2 (fun z => Real.log (A.h z)) z :=
  ((ContDiffOn.contDiffAt hA (HermExtend.isOpen_blocksNe.mem_nhds hz)).log (A.pos z hz).ne').of_le
    (WithTop.coe_le_coe.2 le_top)

end LevelTowerAlt

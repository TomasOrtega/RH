import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturbSemipos
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineSmooth
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineLevi
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace PerturbedSemipositivity

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Establish `hopen : ∀ k, ∀ᶠ y in 𝓝 z, ∃ i, y ⟨k, i⟩ ≠ 0` using `fun k => by`. Take `⟨i, hi⟩` from `hz k`. Conclude with `Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi) fun y hy => ⟨i, hy⟩`. Conclude with `Filter.eventually_all.mpr hopen`.
-/
theorem blocks_mem_nhds {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    {y : (Σ k, ι k) → ℂ | ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0} ∈ 𝓝 z := by
  have hopen : ∀ k, ∀ᶠ y in 𝓝 z, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi)
      fun y hy => ⟨i, hy⟩
  exact Filter.eventually_all.mpr hopen

/- English proof (translation)
Establish `h` using `hA.contDiffAt (blocks_mem_nhds hz)`. Conclude with `(h.of_le (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top)).log (A.pos z hz).ne'`.
-/
theorem contDiffAt_log_h (A : HermLine ι) (hA : IsSmoothHerm A) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContDiffAt ℝ 2 (fun y => Real.log (A.h y)) z := by
  have h := hA.contDiffAt (blocks_mem_nhds hz)
  exact (h.of_le (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top)).log (A.pos z hz).ne'

/- English proof (translation)
Establish `h` using `ReciprocityTheory.AnForm.levi_add_smul (f := fun _ => (0 : ℝ)) (g := f) c contDiffAt_const hf w`. Establish `h0 : ReciprocityTheory.AnForm.levi (fun _ : (Σ k, ι k) → ℂ => (0 : ℝ)) z w = 0`. Simplify using `[ReciprocityTheory.AnForm.levi]`. Simplify using `only [zero_add] at h`. Rewrite using `[h, h0, zero_add]`.
-/
theorem levi_const_mul {f : ((Σ k, ι k) → ℂ) → ℝ} {z : (Σ k, ι k) → ℂ} (c : ℝ) (hf : ContDiffAt ℝ 2 f z)
    (w : (Σ k, ι k) → ℂ) :
    ReciprocityTheory.AnForm.levi (fun y => c * f y) z w = c * ReciprocityTheory.AnForm.levi f z w := by
  have h := ReciprocityTheory.AnForm.levi_add_smul (f := fun _ => (0 : ℝ)) (g := f) c contDiffAt_const hf w
  have h0 : ReciprocityTheory.AnForm.levi (fun _ : (Σ k, ι k) → ℂ => (0 : ℝ)) z w = 0 := by
    simp [ReciprocityTheory.AnForm.levi]
  simp only [zero_add] at h
  rw [h, h0, zero_add]

end PerturbedSemipositivity

open PerturbedSemipositivity in

/- English proof (translation)
Introduce `K _ ι _ P0 P M b a hM hb ha`. Take `⟨m, rfl⟩` from `Int.eq_ofNat_of_zero_le hb`. Take `⟨n, rfl⟩` from `Int.eq_ofNat_of_zero_le ha`. Establish `hH : IsSmoothHerm (fsH ι)` using `FsLineSmooth.proof K ι`. Establish `hfun : (HermLine.zcomb M (fsH ι) m n).h = fun y => M.h y ^ m * (fsH ι).h y ^ n`.

Use function extensionality and compare the values at `y`. Simplify using `[HermLine.zcomb]`. Use `⟨?_, fun z hz w hw => ?_⟩` and prove the remaining obligations. Establish `hMs : IsSmoothHerm M` using `hM.1`. Unfold `IsSmoothHerm at hMs hH ⊢`.

Rewrite using `[hfun]`. Conclude with `(hMs.pow m).mul (hH.pow n)`. Establish `hz'` using `hz.1`. Establish `hev : (fun y => Real.log ((HermLine.zcomb M (fsH ι) m n).h y)) =ᶠ[𝓝 z] fun y => (m : ℝ) * Real.log (M.h y) + (n : ℝ) * Real.log ((fsH ι).h y)` using `by filter_upwards [blocks_mem_nhds hz'] with y hy`. Rewrite using `[hfun, Real.log_mul (pow_ne_zero _ (M.pos y hy).ne') (pow_ne_zero _ ((fsH ι).pos y hy).ne'), Real.log_pow, Real.log_pow]`.

Establish `hfM` using `contDiffAt_log_h M hM.1 hz'`. Establish `hfH` using `contDiffAt_log_h (fsH ι) hH hz'`. Establish `hadd` using `ReciprocityTheory.AnForm.levi_add_smul (f := fun y => (m : ℝ) * Real.log (M.h y)) (g := fun y => Real.log ((fsH ι).h y)) (n : ℝ) (contDiffAt_const.mul hfM) hfH w`. Use `beta_reduce at hadd`. Establish `h1 : 0 ≤ leviForm (fun y => Real.log (M.h y)) z w` using `hM.2 z hz w hw`.

Establish `h2 : 0 ≤ leviForm (fun y => Real.log ((fsH ι).h y)) z w` using `FsLineLevi.proof K ι z w hz'`. Express the relevant statement in the definitionally equal form `0 ≤ ReciprocityTheory.AnForm.levi _ z w`. Rewrite using `[ReciprocityTheory.AnForm.levi_congr hev, hadd, levi_const_mul (m : ℝ) hfM w]`. Conclude with `add_nonneg (mul_nonneg (Nat.cast_nonneg m) h1) (mul_nonneg (Nat.cast_nonneg n) h2)`.
-/
theorem PerturbSemipos.proof : PerturbSemipos.Statement := by
  intro K _ ι _ P0 P M b a hM hb ha
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  have hH : IsSmoothHerm (fsH ι) := FsLineSmooth.proof K ι
  have hfun : (HermLine.zcomb M (fsH ι) m n).h = fun y => M.h y ^ m * (fsH ι).h y ^ n := by
    funext y
    simp [HermLine.zcomb]
  refine ⟨?_, fun z hz w hw => ?_⟩
  · have hMs : IsSmoothHerm M := hM.1
    unfold IsSmoothHerm at hMs hH ⊢
    rw [hfun]
    exact (hMs.pow m).mul (hH.pow n)
  · have hz' := hz.1
    have hev : (fun y => Real.log ((HermLine.zcomb M (fsH ι) m n).h y)) =ᶠ[𝓝 z]
        fun y => (m : ℝ) * Real.log (M.h y) + (n : ℝ) * Real.log ((fsH ι).h y) := by
      filter_upwards [blocks_mem_nhds hz'] with y hy
      rw [hfun, Real.log_mul (pow_ne_zero _ (M.pos y hy).ne') (pow_ne_zero _ ((fsH ι).pos y hy).ne'),
        Real.log_pow, Real.log_pow]
    have hfM := contDiffAt_log_h M hM.1 hz'
    have hfH := contDiffAt_log_h (fsH ι) hH hz'
    have hadd := ReciprocityTheory.AnForm.levi_add_smul (f := fun y => (m : ℝ) * Real.log (M.h y))
      (g := fun y => Real.log ((fsH ι).h y)) (n : ℝ) (contDiffAt_const.mul hfM) hfH w
    beta_reduce at hadd
    have h1 : 0 ≤ leviForm (fun y => Real.log (M.h y)) z w := hM.2 z hz w hw
    have h2 : 0 ≤ leviForm (fun y => Real.log ((fsH ι).h y)) z w := FsLineLevi.proof K ι z w hz'
    change 0 ≤ ReciprocityTheory.AnForm.levi _ z w
    rw [ReciprocityTheory.AnForm.levi_congr hev, hadd, levi_const_mul (m : ℝ) hfM w]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg m) h1) (mul_nonneg (Nat.cast_nonneg n) h2)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

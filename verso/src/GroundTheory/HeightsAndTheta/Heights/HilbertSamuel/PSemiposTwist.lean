import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturb
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineLevi
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineSmooth
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

/- English proof (translation)
Introduce `K _ ι _ P0 P L p q hL`. Use `set U : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} with hU`. Establish `hUo : IsOpen U`. Establish `e : U = ⋂ k, ⋃ i, {z : (Σ k, ι k) → ℂ | z ⟨k, i⟩ ≠ 0}`. Use extensionality with `z`.

Simplify using `[hU]`. Rewrite using `[e]`. Conclude with `isOpen_iInter_of_finite fun k => isOpen_iUnion fun i => (continuous_apply _).isOpen_preimage _ isOpen_ne`. Establish `hH : IsSmoothHerm (fsH ι)` using `FsLineSmooth.proof K ι`. Establish `hsm : IsSmoothHerm (HermLine.zcomb L (fsH ι) q p)`.

Establish `e : (HermLine.zcomb L (fsH ι) q p).h = fun z => L.h z ^ q * (fsH ι).h z ^ p`. Use function extensionality and compare the values at `z`. Use `show L.h z ^ (q : ℤ) * (fsH ι).h z ^ (p : ℤ) = _`. Rewrite using `[zpow_natCast, zpow_natCast]`. Unfold `IsSmoothHerm`.

Rewrite using `[e]`. Conclude with `(hL.1.pow q).mul (hH.pow p)`. Use `⟨hsm, fun z hz w hw => ?_⟩` and prove the remaining obligations. Establish `hzU : z ∈ U` using `hz.1`. Establish `hlog : ∀ A : HermLine ι, IsSmoothHerm A → ContDiffAt ℝ 2 (fun y => Real.log (A.h y)) z` using `fun A hA => ((hA.contDiffAt (hUo.mem_nhds hzU)).of_le (WithTop.coe_le_coe.2 le_top)).log (A.pos z hzU).ne'`.

Establish `h1` using `hlog L hL.1`. Establish `h2` using `hlog (fsH ι) hH`. Establish `hev : (fun y => Real.log ((HermLine.zcomb L (fsH ι) q p).h y)) =ᶠ[𝓝 z] fun y => (0 + (q : ℝ) * Real.log (L.h y)) + (p : ℝ) * Real.log ((fsH ι).h y)` using `by filter_upwards [hUo.mem_nhds hzU] with y hy show Real.log (L.h y ^ (q : ℤ) * (fsH ι).h y ^ (p : ℤ)) = _`. Rewrite using `[Real.log_mul (zpow_pos (L.pos y hy) _).ne' (zpow_pos ((fsH ι).pos y hy) _).ne', Real.log_zpow, Real.log_zpow]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hLz : 0 ≤ ReciprocityTheory.AnForm.levi (fun y => Real.log (L.h y)) z w` using `hL.2 z hz w hw`. Establish `hHz : 0 ≤ ReciprocityTheory.AnForm.levi (fun y => Real.log ((fsH ι).h y)) z w` using `FsLineLevi.proof K ι z w hzU`. Establish `e1` using `ReciprocityTheory.AnForm.levi_add_smul (f := fun y => 0 + (q : ℝ) * Real.log (L.h y)) (g := fun y => Real.log ((fsH ι).h y)) (p : ℝ) (contDiffAt_const.add (contDiffAt_const.mul h1)) h2 w`. Establish `e2` using `ReciprocityTheory.AnForm.levi_add_smul (f := fun _ => (0 : ℝ)) (g := fun y => Real.log (L.h y)) (q : ℝ) contDiffAt_const h1 w`.

Establish `hl0 : ReciprocityTheory.AnForm.levi (fun _ => (0 : ℝ)) z w = 0` using `by simp [ReciprocityTheory.AnForm.levi]`. Express the relevant statement in the definitionally equal form `0 ≤ ReciprocityTheory.AnForm.levi _ z w`. Rewrite using `[ReciprocityTheory.AnForm.levi_congr hev, e1, e2, hl0]`. Establish `a1` using `mul_nonneg (Nat.cast_nonneg (α := ℝ) q) hLz`. Establish `a2` using `mul_nonneg (Nat.cast_nonneg (α := ℝ) p) hHz`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem SemiposTwist.proof : SemiposTwist.Statement := by
  intro K _ ι _ P0 P L p q hL
  set U : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} with hU
  have hUo : IsOpen U := by
    have e : U = ⋂ k, ⋃ i, {z : (Σ k, ι k) → ℂ | z ⟨k, i⟩ ≠ 0} := by
      ext z
      simp [hU]
    rw [e]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_iUnion fun i => (continuous_apply _).isOpen_preimage _ isOpen_ne
  have hH : IsSmoothHerm (fsH ι) := FsLineSmooth.proof K ι
  have hsm : IsSmoothHerm (HermLine.zcomb L (fsH ι) q p) := by
    have e : (HermLine.zcomb L (fsH ι) q p).h = fun z => L.h z ^ q * (fsH ι).h z ^ p := by
      funext z
      show L.h z ^ (q : ℤ) * (fsH ι).h z ^ (p : ℤ) = _
      rw [zpow_natCast, zpow_natCast]
    unfold IsSmoothHerm
    rw [e]
    exact (hL.1.pow q).mul (hH.pow p)
  refine ⟨hsm, fun z hz w hw => ?_⟩
  have hzU : z ∈ U := hz.1
  have hlog : ∀ A : HermLine ι, IsSmoothHerm A → ContDiffAt ℝ 2 (fun y => Real.log (A.h y)) z :=
    fun A hA => ((hA.contDiffAt (hUo.mem_nhds hzU)).of_le (WithTop.coe_le_coe.2 le_top)).log
      (A.pos z hzU).ne'
  have h1 := hlog L hL.1
  have h2 := hlog (fsH ι) hH
  have hev : (fun y => Real.log ((HermLine.zcomb L (fsH ι) q p).h y)) =ᶠ[𝓝 z]
      fun y => (0 + (q : ℝ) * Real.log (L.h y)) + (p : ℝ) * Real.log ((fsH ι).h y) := by
    filter_upwards [hUo.mem_nhds hzU] with y hy
    show Real.log (L.h y ^ (q : ℤ) * (fsH ι).h y ^ (p : ℤ)) = _
    rw [Real.log_mul (zpow_pos (L.pos y hy) _).ne' (zpow_pos ((fsH ι).pos y hy) _).ne',
      Real.log_zpow, Real.log_zpow]
    push_cast
    ring
  have hLz : 0 ≤ ReciprocityTheory.AnForm.levi (fun y => Real.log (L.h y)) z w := hL.2 z hz w hw
  have hHz : 0 ≤ ReciprocityTheory.AnForm.levi (fun y => Real.log ((fsH ι).h y)) z w :=
    FsLineLevi.proof K ι z w hzU
  have e1 := ReciprocityTheory.AnForm.levi_add_smul (f := fun y => 0 + (q : ℝ) * Real.log (L.h y))
    (g := fun y => Real.log ((fsH ι).h y)) (p : ℝ) (contDiffAt_const.add (contDiffAt_const.mul h1)) h2 w
  have e2 := ReciprocityTheory.AnForm.levi_add_smul (f := fun _ => (0 : ℝ))
    (g := fun y => Real.log (L.h y)) (q : ℝ) contDiffAt_const h1 w
  have hl0 : ReciprocityTheory.AnForm.levi (fun _ => (0 : ℝ)) z w = 0 := by simp [ReciprocityTheory.AnForm.levi]
  change 0 ≤ ReciprocityTheory.AnForm.levi _ z w
  rw [ReciprocityTheory.AnForm.levi_congr hev, e1, e2, hl0]
  have a1 := mul_nonneg (Nat.cast_nonneg (α := ℝ) q) hLz
  have a2 := mul_nonneg (Nat.cast_nonneg (α := ℝ) p) hHz
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

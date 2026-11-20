import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

namespace GlobalTheory.LUNear

open ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf Metric

/- English proof (translation)
Introduce `E _ _ _ r X x hx δ hδ`. Establish `hdom : x ∈ X.dom` using `KU.orth_dom X hx`. Establish `hU : IsOpen (cellL X x)` using `(FourierCoefficientDomain.isOpen_dom X).inter (isOpen_ne_fun (Delta_diff (x0 := x)).continuous continuous_const)`. Establish `hxU : x ∈ cellL X x` using `⟨hdom, by rw [orthogonalFrame_delta_eq_one hx]; exact one_ne_zero⟩`. Establish `hz0 : zF X x x = 0`.

Establish `h` using `(uniq_all hx (z := 0) (ExtFPf.oneF_mem X)).2.1`. Rewrite `h` using `[PoinPf.cpt_zero, ExtFPf.rmul_oneF]`. Then use the resulting hypothesis. Establish `hzc : ContinuousAt (zF X x) x` using `((zF_diffOn (x0 := x)).continuousOn).continuousAt (hU.mem_nhds hxU)`. Establish `hS : {y | y ∈ cellL X x ∧ ‖zF X x y‖ < δ} ∈ 𝓝 x`. Use `Filter.inter_mem (hU.mem_nhds hxU) ?_` and prove the remaining obligations.

Establish `: ∀ᶠ y in 𝓝 x, ‖zF X x y‖ < δ` using `hzc.norm.eventually (Iio_mem_nhds (by show ‖zF X x x‖ < δ; rw [hz0, norm_zero]; exact hδ))`. Conclude with `this`. Set `g : Frame X.Ψ r → Frame X.Ψ r` to `fun M τ a c => ∑ k, M τ a k * x τ k c`. Establish `hg : Continuous g`. Use `continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c => ?_` and prove the remaining obligations.

Use `continuous_finset_sum _ fun k _ => ?_` and prove the remaining obligations. Use `fun_prop`. Establish `hg1 : g (ExtFPf.oneF X) = x`. Use function extensionality and compare the values at `τ a c`. Simplify using `[g, ExtFPf.oneF, Matrix.one_apply]`.

Establish `hpre : g ⁻¹' {y | y ∈ cellL X x ∧ ‖zF X x y‖ < δ} ∈ 𝓝 (ExtFPf.oneF X)`. Use `hg.continuousAt.preimage_mem_nhds ?_` and prove the remaining obligations. Rewrite using `[hg1]`. Conclude with `hS`. Take `⟨ε, hε, hball⟩` from `Metric.mem_nhds_iff.mp hpre`.

Use `⟨ε, hε, fun m hm => ?_⟩` and prove the remaining obligations. Set `M : Frame X.Ψ r` to `fun τ a c => m τ a c`. Establish `hM : M ∈ ball (ExtFPf.oneF X) ε`. Rewrite using `[mem_ball, dist_pi_lt_iff hε]`. Introduce `τ`.

Rewrite using `[dist_pi_lt_iff hε]`. Introduce `a`. Rewrite using `[dist_pi_lt_iff hε]`. Introduce `c`. Rewrite using `[dist_eq_norm]`.

Conclude with `hm τ a c`. Establish `hgM : X.lmulC m x = g M`. Use function extensionality and compare the values at `τ a c`. Both sides reduce to the same expression. Take `⟨⟨hyd, hyΔ⟩, hyz⟩` from `hball hM`.

Use `⟨zF X x (g M), hyz, bF X x (g M), bF_mem hyd hyΔ, ?_⟩` and prove the remaining obligations. Rewrite using `[hgM]`. Conclude with `split_eq hx (g M)`.
-/
theorem lmulC_split_near_one :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r),
      IsOrth X x → ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ m : X.Ψ → Matrix (Fin r) (Fin r) ℂ,
        (∀ τ a b, ‖m τ a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < ε) →
          ∃ z : V (nd X), ‖z‖ < δ ∧ ∃ b ∈ Bor X.Ψ r, X.lmulC m x = rmul (cpt X x z) b := by
  intro E _ _ _ r X x hx δ hδ
  have hdom : x ∈ X.dom := KU.orth_dom X hx
  have hU : IsOpen (cellL X x) :=
    (FourierCoefficientDomain.isOpen_dom X).inter (isOpen_ne_fun (Delta_diff (x0 := x)).continuous continuous_const)
  have hxU : x ∈ cellL X x := ⟨hdom, by rw [orthogonalFrame_delta_eq_one hx]; exact one_ne_zero⟩
  have hz0 : zF X x x = 0 := by
    have h := (uniq_all hx (z := 0) (ExtFPf.oneF_mem X)).2.1
    rwa [PoinPf.cpt_zero, ExtFPf.rmul_oneF] at h
  have hzc : ContinuousAt (zF X x) x :=
    ((zF_diffOn (x0 := x)).continuousOn).continuousAt (hU.mem_nhds hxU)
  have hS : {y | y ∈ cellL X x ∧ ‖zF X x y‖ < δ} ∈ 𝓝 x := by
    refine Filter.inter_mem (hU.mem_nhds hxU) ?_
    have : ∀ᶠ y in 𝓝 x, ‖zF X x y‖ < δ :=
      hzc.norm.eventually (Iio_mem_nhds (by show ‖zF X x x‖ < δ; rw [hz0, norm_zero]; exact hδ))
    exact this

  let g : Frame X.Ψ r → Frame X.Ψ r := fun M τ a c => ∑ k, M τ a k * x τ k c
  have hg : Continuous g := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c => ?_
    refine continuous_finset_sum _ fun k _ => ?_
    fun_prop
  have hg1 : g (ExtFPf.oneF X) = x := by
    funext τ a c
    simp [g, ExtFPf.oneF, Matrix.one_apply]
  have hpre : g ⁻¹' {y | y ∈ cellL X x ∧ ‖zF X x y‖ < δ} ∈ 𝓝 (ExtFPf.oneF X) := by
    refine hg.continuousAt.preimage_mem_nhds ?_
    rw [hg1]; exact hS
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨ε, hε, fun m hm => ?_⟩
  let M : Frame X.Ψ r := fun τ a c => m τ a c
  have hM : M ∈ ball (ExtFPf.oneF X) ε := by
    rw [mem_ball, dist_pi_lt_iff hε]; intro τ
    rw [dist_pi_lt_iff hε]; intro a
    rw [dist_pi_lt_iff hε]; intro c
    rw [dist_eq_norm]
    exact hm τ a c
  have hgM : X.lmulC m x = g M := by
    funext τ a c
    rfl
  obtain ⟨⟨hyd, hyΔ⟩, hyz⟩ := hball hM
  refine ⟨zF X x (g M), hyz, bF X x (g M), bF_mem hyd hyΔ, ?_⟩
  rw [hgM]
  exact split_eq hx (g M)

end GlobalTheory.LUNear

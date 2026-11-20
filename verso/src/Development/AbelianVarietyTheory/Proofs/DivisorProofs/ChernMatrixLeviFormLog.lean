import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensDetWeightEqNegLeviLog
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixDens

/- English proof (translation)
Establish `hξ : ξ = ∑ j, ξ j • EuclideanSpace.single j (1 : ℂ)`. Use extensionality with `i`. Simplify using `[Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']`. Use `conv_rhs => rw [hξ]`. Simplify using `only [map_sum, ContinuousLinearMap.sum_apply, map_smul, map_smulₛₗ, ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_mul_apply_single_mul_conj {D : ℕ} (B : V D →L[ℂ] V D →L⋆[ℂ] ℂ) (ξ : V D) :
    ∑ j, ∑ l, ξ j * B (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) * starRingEnd ℂ (ξ l) = B ξ ξ := by
  have hξ : ξ = ∑ j, ξ j • EuclideanSpace.single j (1 : ℂ) := by
    ext i
    simp [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  conv_rhs => rw [hξ]
  simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul, map_smulₛₗ, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/- English proof (translation)
Introduce `k _ X p σ D L g hg U t ht c y hy hU ξ`. Set `c₀ : VB.Chart L 1` to `⟨U, fun _ => t, ht⟩`. Establish `hi : y ∈ ptsIn p σ ((det L 1).U c₀)` using `hU`. Establish `ho` using `ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) U)`. Establish `hm` using `ChartGlue.mem_over c.e hy hU`.

Establish `e : (fun v => ((g.detWeight.φ c₀ (c.e.symm v) : ℝ) : ℂ)) =ᶠ[𝓝 (c.e y)] fun v => -((Real.log (g.form t t (c.e.symm v)).re : ℝ) : ℂ)` using `by filter_upwards [ho.mem_nhds hm] with v hv`. Rewrite using `[← Complex.ofReal_neg]`. Use `congr 1`. Use `show -Real.log (g.G c₀ (c.e.symm v)).det.re = -Real.log (g.form t t (c.e.symm v)).re`. Rewrite using `[Matrix.det_unique, ← g.form_frame c₀ hv.2]`.

Establish `hd : ContDiffAt ℝ 2 (fun v => g.detWeight.φ c₀ (c.e.symm v)) (c.e y)` using `hg.detWeight.contDiffAt c hy hi`. Establish `hu` using `(contDiffAt_ofReal_comp hd).congr_of_eventuallyEq e.symm`. Establish `hB : ∀ j l, chernMat g.detWeight c y j l = -leviForm (fun v => Real.log (g.form t t (c.e.symm v)).re) (c.e y) (EuclideanSpace.single j 1) (EuclideanSpace.single l 1)`. Introduce `j l`. Rewrite using `[chernMat, c.hess_eq hg.detWeight hy hi (mem_pick _ y)]`.

Use `show ReciprocityTheory.L2DbarEstimates.cHess D (fun v => ((g.detWeight.φ c₀ (c.e.symm v) : ℝ) : ℂ)) (c.e y) j l = _`. Rewrite using `[ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e, GlobalTheory.CurveDens.cHess_apply_eq_ddbar hu]`. Use `erw [ddbar_neg]`. Both sides reduce to the same expression. Repeatedly rewrite using `[hB, mul_neg, neg_mul, Finset.sum_neg_distrib, sum_mul_apply_single_mul_conj, Complex.neg_re]`.
-/
theorem chernMat_eq_neg_leviForm : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : X.Modules) (g : Met p σ L 1), g.IsCInf → ∀ (U : X.Opens) (t : Γ(L, U)), IsFrame (fun _ : Fin 1 => t) → ∀ (c : AlgChart p σ D), ∀ y ∈ c.e.source, y ∈ ptsIn p σ U → ∀ ξ : V D, (∑ j, ∑ l, ξ j * chernMat g.detWeight c y j l * starRingEnd ℂ (ξ l)).re = -(leviForm (fun v => Real.log (g.form t t (c.e.symm v)).re) (c.e y) ξ ξ).re := by
  intro k _ X p σ D L g hg U t ht c y hy hU ξ
  let c₀ : VB.Chart L 1 := ⟨U, fun _ => t, ht⟩
  have hi : y ∈ ptsIn p σ ((det L 1).U c₀) := hU
  have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) U)
  have hm := ChartGlue.mem_over c.e hy hU
  have e : (fun v => ((g.detWeight.φ c₀ (c.e.symm v) : ℝ) : ℂ)) =ᶠ[𝓝 (c.e y)]
      fun v => -((Real.log (g.form t t (c.e.symm v)).re : ℝ) : ℂ) := by
    filter_upwards [ho.mem_nhds hm] with v hv
    rw [← Complex.ofReal_neg]
    congr 1
    show -Real.log (g.G c₀ (c.e.symm v)).det.re = -Real.log (g.form t t (c.e.symm v)).re
    rw [Matrix.det_unique, ← g.form_frame c₀ hv.2]
  have hd : ContDiffAt ℝ 2 (fun v => g.detWeight.φ c₀ (c.e.symm v)) (c.e y) :=
    hg.detWeight.contDiffAt c hy hi
  have hu := (contDiffAt_ofReal_comp hd).congr_of_eventuallyEq e.symm
  have hB : ∀ j l, chernMat g.detWeight c y j l =
      -leviForm (fun v => Real.log (g.form t t (c.e.symm v)).re) (c.e y)
        (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) := by
    intro j l
    rw [chernMat, c.hess_eq hg.detWeight hy hi (mem_pick _ y)]
    show ReciprocityTheory.L2DbarEstimates.cHess D (fun v => ((g.detWeight.φ c₀ (c.e.symm v) : ℝ) : ℂ)) (c.e y) j l = _
    rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e, GlobalTheory.CurveDens.cHess_apply_eq_ddbar hu]
    erw [ddbar_neg]
    rfl
  simp_rw [hB, mul_neg, neg_mul, Finset.sum_neg_distrib, sum_mul_apply_single_mul_conj, Complex.neg_re]

end GlobalTheory.MixDens

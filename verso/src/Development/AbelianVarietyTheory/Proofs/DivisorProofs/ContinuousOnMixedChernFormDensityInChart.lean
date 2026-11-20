import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxE
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace GlobalTheory.Mix

/- English proof (translation)
Introduce `k _ X p σ D L c y₀ hy₀`. Set `i : ∀ a, (L a).B.ι` to `fun a => pick (L a).φ.isLB y₀`. Set `S : Set (CxPts p σ)` to `c.e.source ∩ ⋂ a, ptsIn p σ ((L a).B.U (i a))`. Establish `hSo : IsOpen S` using `c.e.open_source.inter (isOpen_iInter_of_finite fun a => isOpen_ptsIn _)`. Establish `hy₀S : y₀ ∈ S` using `⟨hy₀, mem_iInter.2 fun a => mem_pick _ y₀⟩`.

Establish `hH : ∀ (a : Fin D) (j l : Fin D), ContinuousOn (fun y => c.hess (L a).φ (i a) y j l) S`. Introduce `a j l`. Establish `hO : IsOpen (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ ((L a).B.U (i a)))` using `isOpen_over c.e (isOpen_ptsIn _)`. Establish `hg : ContDiffOn ℝ ∞ (fun v => ((L a).φ.φ (i a) (c.e.symm v) : ℂ)) (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ ((L a).B.U (i a)))` using `Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_chart ((L a).cInf (i a)) c)`. Establish `hw` using `ReciprocityTheory.L2DbarEstimates.Y.continuousOn_wd_wdb hO hg j l`.

Conclude with `hw.comp (c.e.continuousOn.mono inter_subset_left) fun y hy => ⟨c.e.map_source hy.1, by`. Simplify `mem_iInter.1 hy.2 a⟩` using `only [mem_preimage, c.e.left_inv hy.1]`. Set `F : CxPts p σ → ℝ` to `fun y => (Real.pi ^ D)⁻¹ * (∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => c.hess (L (τ l)).φ (i (τ l)) y j l).det).re`. Establish `hF : ContinuousOn F S`. Use `continuousOn_const.mul (Complex.continuous_re.comp_continuousOn (continuousOn_finsetSum _ fun τ _ => ?_))` and prove the remaining obligations.

Use `(continuous_id.matrix_det).comp_continuousOn ?_` and prove the remaining obligations. Conclude with `continuousOn_pi.2 fun j => continuousOn_pi.2 fun l => hH (τ l) j l`. Establish `he : ∀ y ∈ S, dens L c y = F y`. Introduce `y hy`. Establish `hm : ∀ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => c.hess (L (τ l)).φ (pick (L (τ l)).φ.isLB y) y j l) = Matrix.of fun j l => c.hess (L (τ l)).φ (i (τ l)) y j l` using `fun τ => by`.

Use extensionality with `j l`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[c.hess_eq (L (τ l)).cInf hy.1 (mem_iInter.1 hy.2 (τ l)) (mem_pick _ y)]`. Simplify using `only [dens, F, hm]`. Use `ContinuousAt.continuousWithinAt ?_` and prove the remaining obligations.

Use `(hF.continuousAt (hSo.mem_nhds hy₀S)).congr ?_` and prove the remaining obligations. Use `filter_upwards [hSo.mem_nhds hy₀S] with y hy`. Conclude with `(he y hy).symm`.
-/
theorem continuousOn_dens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ)
    (D : ℕ) (L : Fin D → MLine p σ) (c : AlgChart p σ D), ContinuousOn (dens L c) c.e.source := by
  intro k _ X p σ D L c y₀ hy₀
  let i : ∀ a, (L a).B.ι := fun a => pick (L a).φ.isLB y₀
  let S : Set (CxPts p σ) := c.e.source ∩ ⋂ a, ptsIn p σ ((L a).B.U (i a))
  have hSo : IsOpen S := c.e.open_source.inter (isOpen_iInter_of_finite fun a => isOpen_ptsIn _)
  have hy₀S : y₀ ∈ S := ⟨hy₀, mem_iInter.2 fun a => mem_pick _ y₀⟩
  have hH : ∀ (a : Fin D) (j l : Fin D),
      ContinuousOn (fun y => c.hess (L a).φ (i a) y j l) S := by
    intro a j l
    have hO : IsOpen (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ ((L a).B.U (i a))) :=
      isOpen_over c.e (isOpen_ptsIn _)
    have hg : ContDiffOn ℝ ∞ (fun v => ((L a).φ.φ (i a) (c.e.symm v) : ℂ))
        (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ ((L a).B.U (i a))) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_chart ((L a).cInf (i a)) c)
    have hw := ReciprocityTheory.L2DbarEstimates.Y.continuousOn_wd_wdb hO hg j l
    exact hw.comp (c.e.continuousOn.mono inter_subset_left) fun y hy =>
      ⟨c.e.map_source hy.1, by
        simpa only [mem_preimage, c.e.left_inv hy.1] using mem_iInter.1 hy.2 a⟩
  let F : CxPts p σ → ℝ := fun y => (Real.pi ^ D)⁻¹ * (∑ τ : Equiv.Perm (Fin D),
    (Matrix.of fun j l => c.hess (L (τ l)).φ (i (τ l)) y j l).det).re
  have hF : ContinuousOn F S := by
    refine continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
      (continuousOn_finsetSum _ fun τ _ => ?_))
    refine (continuous_id.matrix_det).comp_continuousOn ?_
    exact continuousOn_pi.2 fun j => continuousOn_pi.2 fun l => hH (τ l) j l
  have he : ∀ y ∈ S, dens L c y = F y := by
    intro y hy
    have hm : ∀ τ : Equiv.Perm (Fin D),
        (Matrix.of fun j l => c.hess (L (τ l)).φ (pick (L (τ l)).φ.isLB y) y j l) =
          Matrix.of fun j l => c.hess (L (τ l)).φ (i (τ l)) y j l := fun τ => by
      ext j l
      simp only [Matrix.of_apply]
      rw [c.hess_eq (L (τ l)).cInf hy.1 (mem_iInter.1 hy.2 (τ l)) (mem_pick _ y)]
    simp only [dens, F, hm]
  refine ContinuousAt.continuousWithinAt ?_
  refine (hF.continuousAt (hSo.mem_nhds hy₀S)).congr ?_
  filter_upwards [hSo.mem_nhds hy₀S] with y hy
  exact (he y hy).symm

end GlobalTheory.Mix

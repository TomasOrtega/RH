import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernRealClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar hermMat eval₂ bas relCot dRel IsRelAcyclic)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder
open GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernTop GlobalTheory.Points
open scoped ComplexConjugate

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FubiniStudyChart

open ReciprocityTheory.L2DbarEstimates (V cHess leviV wd wdb sqNorm projPerp wJac)

/- English proof (translation)
Use `set f : V n → ℝ := fun v => Real.log (sqNorm fun i => g i v) with hf`. Use `set G : V n → ℂ := fun v => ((f v : ℝ) : ℂ) with hG`. Establish `hne : (fun i => g i x) ≠ 0` using `fun h => hb (congrFun h b)`. Establish `hfC : ContDiffAt ℝ 2 f x`. Establish `hs : ContDiffAt ℝ 2 (fun v => ∑ i, Complex.normSq (g i v)) x` using `ContDiffAt.sum fun i _ => ReciprocityTheory.L2DbarEstimates.contDiffAt_normSq_comp (hg i)`.

Conclude with `hs.log (ReciprocityTheory.L2DbarEstimates.sqNorm_pos hne).ne'`. Establish `hg2 : ContDiffAt ℝ 2 G x` using `Complex.ofRealCLM.contDiff.contDiffAt.comp x hfC`. Establish `hgc : (fun w => (starRingEnd ℂ) (G w)) = G` using `funext fun w => by simp [G]`. Establish `hH : (cHess n G x).IsHermitian`. Use extensionality with `j k`.

Simplify using `only [Matrix.conjTranspose_apply, cHess, Matrix.of_apply]`. Use `show (starRingEnd ℂ) (wd n k (wdb n j G) x) = wd n j (wdb n k G) x`. Establish `h1 : (fun w => (starRingEnd ℂ) (wdb n j G w)) = wd n j G`. Use function extensionality and compare the values at `w`. Rewrite using `[← ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.wd_conj' n j G w, hgc]`.

Rewrite using `[← ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.wdb_conj' n k (wdb n j G) x, h1, ReciprocityTheory.L2DbarEstimates.comm_wd_wdb G x hg2 j k]`. Use `Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hH, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hre : star y ⬝ᵥ (cHess n G x *ᵥ y) = leviV n G x (fun k => (starRingEnd ℂ) (y k))`. Simplify using `only [dotProduct, Matrix.mulVec, leviV, cHess, Matrix.of_apply, Finset.mul_sum, Pi.star_apply, Complex.conj_conj]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Simplify using `only [Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hre, hG, hf, ReciprocityTheory.L2DbarEstimates.leviLogNormSq n p g x _ hg hne]`. Use `set ξ : Fin n → ℂ := fun k => (starRingEnd ℂ) (y k) with hξ`. Use `set gx : Fin p → ℂ := fun i => g i x`.

Establish `hpos : 0 < sqNorm gx` using `ReciprocityTheory.L2DbarEstimates.sqNorm_pos hne`. Use `Complex.zero_lt_real.2 (div_pos (ReciprocityTheory.L2DbarEstimates.sqNorm_pos fun h0 => hy ?_) hpos)` and prove the remaining obligations. Use `set w := wJac n p g x *ᵥ ξ with hw`. Rewrite `h0` using `[ReciprocityTheory.L2DbarEstimates.projPerp_mulVec, sub_eq_zero]`. Establish `hwb : w b = 0`.

Simplify using `only [hw, Matrix.mulVec, dotProduct, wJac, hbd, zero_mul, Finset.sum_const_zero]`. Establish `hc : ((sqNorm gx : ℝ) : ℂ)⁻¹ * (star gx ⬝ᵥ w) = 0`. Use `congrFun h0 b` as an intermediate fact. Rewrite `this` using `[hwb, Pi.smul_apply, smul_eq_mul, eq_comm, mul_eq_zero]`. Conclude with `this.resolve_right hb`.

Rewrite `h0` using `[hc, zero_smul]`. Establish `hξ0 : ξ = 0` using `hinj ξ fun a => by`. Use `congrFun h0 a` as an intermediate fact. Simplify `this` using `[hw, Matrix.mulVec, dotProduct, wJac]`. Use function extensionality and compare the values at `k`.

Use `congrFun hξ0 k` as an intermediate fact. Simplify `this` using `[hξ]`.
-/
theorem posDef_cHess_log_sqNorm {n p : ℕ} (g : Fin p → V n → ℂ) (x : V n)
    (hg : ∀ i, ContDiffAt ℂ 2 (g i) x) (b : Fin p) (hb : g b x ≠ 0) (hbd : ∀ j, wd n j (g b) x = 0)
    (hinj : ∀ ξ : Fin n → ℂ, (∀ a, ∑ j, wd n j (g a) x * ξ j = 0) → ξ = 0) :
    (cHess n (fun v => ((Real.log (sqNorm fun i => g i v) : ℝ) : ℂ)) x).PosDef := by
  set f : V n → ℝ := fun v => Real.log (sqNorm fun i => g i v) with hf
  set G : V n → ℂ := fun v => ((f v : ℝ) : ℂ) with hG
  have hne : (fun i => g i x) ≠ 0 := fun h => hb (congrFun h b)
  have hfC : ContDiffAt ℝ 2 f x := by
    have hs : ContDiffAt ℝ 2 (fun v => ∑ i, Complex.normSq (g i v)) x :=
      ContDiffAt.sum fun i _ => ReciprocityTheory.L2DbarEstimates.contDiffAt_normSq_comp (hg i)
    exact hs.log (ReciprocityTheory.L2DbarEstimates.sqNorm_pos hne).ne'
  have hg2 : ContDiffAt ℝ 2 G x := Complex.ofRealCLM.contDiff.contDiffAt.comp x hfC
  have hgc : (fun w => (starRingEnd ℂ) (G w)) = G := funext fun w => by simp [G]
  have hH : (cHess n G x).IsHermitian := by
    ext j k
    simp only [Matrix.conjTranspose_apply, cHess, Matrix.of_apply]
    show (starRingEnd ℂ) (wd n k (wdb n j G) x) = wd n j (wdb n k G) x
    have h1 : (fun w => (starRingEnd ℂ) (wdb n j G w)) = wd n j G := by
      funext w
      rw [← ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.wd_conj' n j G w, hgc]
    rw [← ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.wdb_conj' n k (wdb n j G) x, h1,
      ReciprocityTheory.L2DbarEstimates.comm_wd_wdb G x hg2 j k]
  refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hH, fun y hy => ?_⟩
  have hre : star y ⬝ᵥ (cHess n G x *ᵥ y) = leviV n G x (fun k => (starRingEnd ℂ) (y k)) := by
    simp only [dotProduct, Matrix.mulVec, leviV, cHess, Matrix.of_apply, Finset.mul_sum,
      Pi.star_apply, Complex.conj_conj]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [Complex.star_def]
    ring
  rw [hre, hG, hf, ReciprocityTheory.L2DbarEstimates.leviLogNormSq n p g x _ hg hne]

  set ξ : Fin n → ℂ := fun k => (starRingEnd ℂ) (y k) with hξ
  set gx : Fin p → ℂ := fun i => g i x
  have hpos : 0 < sqNorm gx := ReciprocityTheory.L2DbarEstimates.sqNorm_pos hne
  refine Complex.zero_lt_real.2 (div_pos (ReciprocityTheory.L2DbarEstimates.sqNorm_pos fun h0 => hy ?_) hpos)
  set w := wJac n p g x *ᵥ ξ with hw
  rw [ReciprocityTheory.L2DbarEstimates.projPerp_mulVec, sub_eq_zero] at h0
  have hwb : w b = 0 := by
    simp only [hw, Matrix.mulVec, dotProduct, wJac, hbd, zero_mul, Finset.sum_const_zero]
  have hc : ((sqNorm gx : ℝ) : ℂ)⁻¹ * (star gx ⬝ᵥ w) = 0 := by
    have := congrFun h0 b
    rw [hwb, Pi.smul_apply, smul_eq_mul, eq_comm, mul_eq_zero] at this
    exact this.resolve_right hb
  rw [hc, zero_smul] at h0
  have hξ0 : ξ = 0 := hinj ξ fun a => by
    have := congrFun h0 a
    simpa [hw, Matrix.mulVec, dotProduct, wJac] using this
  funext k
  have := congrFun hξ0 k
  simpa [hξ] using this

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open scoped GlobalTheory.ProjSpace

/- English proof (translation)
Set `e : MvPolynomial (Fin N) k ≃ₐ[k] Γ(PSpace k N, ProjSpace.chart k N i)` to `(MvPolynomial.renameEquiv k (finSuccAboveEquiv i)).trans (ProjSpace.chartAlgEquiv k N i)`. Establish `he : MvPolynomial.eval₂Hom (algX (PSpace.str k N) (ProjSpace.chart k N i)) (fun a => ProjSpace.ratio k N i (i.succAbove a)) = (e : MvPolynomial (Fin N) k →+* _)` using `MvPolynomial.ringHom_ext (fun a => (MvPolynomial.eval₂Hom_C _ _ a).trans (e.commutes a).symm) fun b => (MvPolynomial.eval₂Hom_X' _ _ b).trans ((congrArg (ProjSpace.chartAlgEquiv k N i) (MvPolynomial.rename_X _ b)).trans (ProjSpace.chartAlgEquiv_X k N i (finSuccAboveEquiv i b))).s …`. Rewrite using `[he]`. Conclude with `RingHom.Etale.of_bijective e.bijective`.
-/
theorem etale_ratio (k : Type) [CommRing k] (N : ℕ) (i : Fin (N + 1)) :
    (MvPolynomial.eval₂Hom (algX (PSpace.str k N) (ProjSpace.chart k N i))
      (fun a : Fin N => ProjSpace.ratio k N i (i.succAbove a))).Etale := by
  let e : MvPolynomial (Fin N) k ≃ₐ[k] Γ(PSpace k N, ProjSpace.chart k N i) :=
    (MvPolynomial.renameEquiv k (finSuccAboveEquiv i)).trans (ProjSpace.chartAlgEquiv k N i)
  have he : MvPolynomial.eval₂Hom (algX (PSpace.str k N) (ProjSpace.chart k N i))
      (fun a => ProjSpace.ratio k N i (i.succAbove a)) = (e : MvPolynomial (Fin N) k →+* _) :=
    MvPolynomial.ringHom_ext (fun a => (MvPolynomial.eval₂Hom_C _ _ a).trans (e.commutes a).symm)
      fun b => (MvPolynomial.eval₂Hom_X' _ _ b).trans
        ((congrArg (ProjSpace.chartAlgEquiv k N i) (MvPolynomial.rename_X _ b)).trans
          (ProjSpace.chartAlgEquiv_X k N i (finSuccAboveEquiv i b))).symm
  rw [he]
  exact RingHom.Etale.of_bijective e.bijective

/- English proof (translation)
Use extensionality with `i`. Simplify using `only [ReciprocityTheory.L2DbarEstimates.bas, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, EuclideanSpace.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Apply the tactic sequence `try simp`.
-/
theorem toLp_eq_sum_bas (N : ℕ) (ξ : Fin N → ℂ) :
    (WithLp.toLp 2 ξ : V N) = ∑ j, ξ j • ReciprocityTheory.L2DbarEstimates.bas N j := by
  ext i
  simp only [ReciprocityTheory.L2DbarEstimates.bas, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    EuclideanSpace.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  try simp

/- English proof (translation)
Introduce `k _ N σ c0 z hz b hb`. Express the relevant statement in the definitionally equal form `Fin (N + 1) at b`. Express the relevant statement in the definitionally equal form `z ∈ ptsIn (PSpace.str k N) σ (ProjSpace.chart k N b) at hb`. Use `set g : Fin (N + 1) → V N → ℂ := fun a v => ev (PSpace.str k N) σ (ProjSpace.chart k N b) (ProjSpace.ratio k N b a) (c0.e.symm v) with hg`. Establish `e1 : c0.hess ((ProjSpace.hermitianTwistingSheaf k N).φ σ) b z = cHess N (fun v => ((Real.log (sqNorm fun i => g i v) : ℝ) : ℂ)) (c0.e z)` using `by show cHess N _ _ = _`.

Use `congr 1`. Use function extensionality and compare the values at `v`. Establish `h` using `Weight.fsBasis_φ (p := PSpace.str k N) (σ := σ) (ProjSpace.O1_isLB k N) (ProjSpace.coord k N) (ProjSpace.iSup_nonzeroLocus_coord k N) 1 (by simp) b (c0.e.symm v)`. Use `congrArg (fun r : ℝ => (r : ℂ)) (h.trans ?_)` and prove the remaining obligations. Simplify using `[sqNorm, Matrix.one_apply, Complex.normSq_eq_norm_sq, g, ev]`.

Rewrite using `[e1]`. Use `set x0 := c0.e z with hx0`. Use `set S := c0.e.target ∩ c0.e.symm ⁻¹' ptsIn (PSpace.str k N) σ (ProjSpace.chart k N b) with hS`. Establish `hSo : IsOpen S` using `GlobalTheory.ChartGlue.isOpen_over c0.e (isOpen_ptsIn _)`. Establish `hxS : x0 ∈ S` using `GlobalTheory.ChartGlue.mem_over c0.e hz hb`.

Establish `hgd : ∀ a, DifferentiableOn ℂ (g a) S` using `fun a => c0.holo _ _`. Establish `hgC : ∀ a, ContDiffAt ℂ 2 (g a) x0` using `fun a => ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn N _ S hSo (hgd a)).contDiffAt (hSo.mem_nhds hxS)).of_le (by norm_cast)`. Establish `hgD : ∀ a, DifferentiableAt ℂ (g a) x0` using `fun a => (hgd a).differentiableAt (hSo.mem_nhds hxS)`. Establish `hb1 : g b =ᶠ[nhds x0] fun _ => 1` using `by filter_upwards [hSo.mem_nhds hxS] with v hv`. Simplify using `only [hg, ProjSpace.ratio, ProjSpace.ratioOn_self]`.

Rewrite using `[ev_eq hv.2, map_one]`. Use `posDef_cHess_log_sqNorm g x0 hgC b ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[hb1.eq_of_nhds]`. Conclude with `one_ne_zero`. Introduce `j`.

Rewrite using `[ReciprocityTheory.L2DbarEstimates.wd_of_differentiableAt (hgD b), hb1.fderiv_eq]`. Simplify using the standard rewrite rules. Introduce `ξ hξ`. Take `⟨⟨e, U, hU, x, hx, h₁, h₂, h₃⟩, hzs, hU', hx'⟩` from `AlgChart.exists_of_etale (σ := σ) (ProjSpace.isAffineOpen_chart k N b) (fun a => ProjSpace.ratio k N b (b.succAbove a)) (etale_ratio k N b) hb`. Simplify using `only at hU'`.

Substitute `hU'` using the available equality. Simplify using `only at hx'`. Substitute `hx'` using the available equality. Use `set cs : AlgChart (PSpace.str k N) σ N := ⟨e, _, hU, _, hx, h₁, h₂, h₃⟩ with hcs`. Use `set F : V N → V N := cs.e ∘ c0.e.symm with hF`.

Use `set F' : V N → V N := c0.e ∘ cs.e.symm with hF'`. Use `set T := c0.e.target ∩ c0.e.symm ⁻¹' cs.e.source with hT`. Establish `hTo : IsOpen T` using `GlobalTheory.ChartGlue.isOpen_over c0.e cs.e.open_source`. Establish `hxT : x0 ∈ T` using `GlobalTheory.ChartGlue.mem_over c0.e hz hzs`. Establish `hFd : DifferentiableAt ℂ F x0` using `(c0.holo_trans cs).differentiableAt (hTo.mem_nhds hxT)`.

Establish `hFx : F x0 = cs.e z` using `by simp only [hF, Function.comp_apply, hx0, c0.e.left_inv hz]`. Establish `hT' : IsOpen (cs.e.target ∩ cs.e.symm ⁻¹' c0.e.source)` using `GlobalTheory.ChartGlue.isOpen_over cs.e c0.e.open_source`. Establish `hF'd : DifferentiableAt ℂ F' (F x0)` using `hFx ▸ (cs.holo_trans c0).differentiableAt (hT'.mem_nhds (GlobalTheory.ChartGlue.mem_over cs.e hzs hz))`. Establish `hid : F' ∘ F =ᶠ[nhds x0] id` using `by filter_upwards [hTo.mem_nhds hxT] with v hv`. Simplify using `only [hF, hF', Function.comp_apply, id, cs.e.left_inv hv.2, c0.e.right_inv hv.1]`.

Establish `hcomp : HasFDerivAt id ((fderiv ℂ F' (F x0)).comp (fderiv ℂ F x0)) x0` using `(hF'd.hasFDerivAt.comp x0 hFd.hasFDerivAt).congr_of_eventuallyEq hid.symm`. Establish `hone` using `hcomp.unique (hasFDerivAt_id x0)`. Use `set w : V N := WithLp.toLp 2 ξ with hw`. Establish `hwsum : w = ∑ j, ξ j • ReciprocityTheory.L2DbarEstimates.bas N j`. Conclude with `toLp_eq_sum_bas N ξ`.

Establish `hgw : ∀ a, fderiv ℂ (g a) x0 w = 0` using `fun a => by`. Use `hξ a` as an intermediate fact. Simplify using `only [ReciprocityTheory.L2DbarEstimates.wd_of_differentiableAt (hgD a)] at this`. Rewrite using `[hwsum, map_sum]`. Simplify `this` using `[mul_comm]`.

Establish `hdF : fderiv ℂ F x0 w = 0`. Use extensionality with `a`. Establish `hFa : HasFDerivAt (fun v => (F v).ofLp a) ((EuclideanSpace.proj (𝕜` using `ℂ) a).comp (fderiv ℂ F x0)) x0 := (EuclideanSpace.proj (𝕜 := ℂ) a).hasFDerivAt.comp x0 hFd.hasFDerivAt`. Establish `heq : (fun v => (F v).ofLp a) =ᶠ[nhds x0] g (b.succAbove a)` using `by filter_upwards [hTo.mem_nhds hxT] with v hv`. Conclude with `h₂ _ hv.2 a`.

Use `(hFa.congr_of_eventuallyEq heq.symm).fderiv` as an intermediate fact. Establish `h2` using `hgw (b.succAbove a)`. Rewrite `h2` using `[this]`. Simplify using `using h2`. Establish `hw0 : w = 0`.

Use `congrArg (fun L : V N →L[ℂ] V N => L w) hone` as an intermediate fact. Simplify using `only [ContinuousLinearMap.comp_apply, hdF, map_zero, ContinuousLinearMap.id_apply] at this`. Conclude with `this.symm`. Use function extensionality and compare the values at `j`. Use `congrArg (fun u : V N => u.ofLp j) hw0` as an intermediate fact.

Simplify `this` using `[hw]`.
-/
theorem fubiniStudy_hessian_posDef : ∀ (k : Type) [CommRing k] (N : ℕ) (σ : k →+* ℂ) (c0 : AlgChart (PSpace.str k N) σ N) (z : CxPts (PSpace.str k N) σ), z ∈ c0.e.source → ∀ (b : (ProjSpace.hermitianTwistingSheaf k N).B.ι), z ∈ ptsIn (PSpace.str k N) σ ((ProjSpace.hermitianTwistingSheaf k N).B.U b) → (c0.hess ((ProjSpace.hermitianTwistingSheaf k N).φ σ) b z).PosDef := by
  intro k _ N σ c0 z hz b hb
  change Fin (N + 1) at b
  change z ∈ ptsIn (PSpace.str k N) σ (ProjSpace.chart k N b) at hb
  set g : Fin (N + 1) → V N → ℂ := fun a v =>
    ev (PSpace.str k N) σ (ProjSpace.chart k N b) (ProjSpace.ratio k N b a) (c0.e.symm v) with hg
  have e1 : c0.hess ((ProjSpace.hermitianTwistingSheaf k N).φ σ) b z =
      cHess N (fun v => ((Real.log (sqNorm fun i => g i v) : ℝ) : ℂ)) (c0.e z) := by
    show cHess N _ _ = _
    congr 1
    funext v
    have h := Weight.fsBasis_φ (p := PSpace.str k N) (σ := σ) (ProjSpace.O1_isLB k N) (ProjSpace.coord k N)
      (ProjSpace.iSup_nonzeroLocus_coord k N) 1 (by simp) b (c0.e.symm v)
    refine congrArg (fun r : ℝ => (r : ℂ)) (h.trans ?_)
    simp [sqNorm, Matrix.one_apply, Complex.normSq_eq_norm_sq, g, ev]
  rw [e1]
  set x0 := c0.e z with hx0
  set S := c0.e.target ∩ c0.e.symm ⁻¹' ptsIn (PSpace.str k N) σ (ProjSpace.chart k N b) with hS
  have hSo : IsOpen S := GlobalTheory.ChartGlue.isOpen_over c0.e (isOpen_ptsIn _)
  have hxS : x0 ∈ S := GlobalTheory.ChartGlue.mem_over c0.e hz hb
  have hgd : ∀ a, DifferentiableOn ℂ (g a) S := fun a => c0.holo _ _
  have hgC : ∀ a, ContDiffAt ℂ 2 (g a) x0 := fun a =>
    ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn N _ S hSo (hgd a)).contDiffAt
      (hSo.mem_nhds hxS)).of_le (by norm_cast)
  have hgD : ∀ a, DifferentiableAt ℂ (g a) x0 := fun a => (hgd a).differentiableAt (hSo.mem_nhds hxS)
  have hb1 : g b =ᶠ[nhds x0] fun _ => 1 := by
    filter_upwards [hSo.mem_nhds hxS] with v hv
    simp only [hg, ProjSpace.ratio, ProjSpace.ratioOn_self]
    rw [ev_eq hv.2, map_one]
  refine posDef_cHess_log_sqNorm g x0 hgC b ?_ ?_ ?_
  · rw [hb1.eq_of_nhds]; exact one_ne_zero
  · intro j
    rw [ReciprocityTheory.L2DbarEstimates.wd_of_differentiableAt (hgD b), hb1.fderiv_eq]
    simp
  · intro ξ hξ
    obtain ⟨⟨e, U, hU, x, hx, h₁, h₂, h₃⟩, hzs, hU', hx'⟩ := AlgChart.exists_of_etale (σ := σ)
      (ProjSpace.isAffineOpen_chart k N b) (fun a => ProjSpace.ratio k N b (b.succAbove a))
      (etale_ratio k N b) hb
    dsimp only at hU'
    subst hU'
    dsimp only at hx'
    subst hx'
    set cs : AlgChart (PSpace.str k N) σ N := ⟨e, _, hU, _, hx, h₁, h₂, h₃⟩ with hcs
    set F : V N → V N := cs.e ∘ c0.e.symm with hF
    set F' : V N → V N := c0.e ∘ cs.e.symm with hF'
    set T := c0.e.target ∩ c0.e.symm ⁻¹' cs.e.source with hT
    have hTo : IsOpen T := GlobalTheory.ChartGlue.isOpen_over c0.e cs.e.open_source
    have hxT : x0 ∈ T := GlobalTheory.ChartGlue.mem_over c0.e hz hzs
    have hFd : DifferentiableAt ℂ F x0 := (c0.holo_trans cs).differentiableAt (hTo.mem_nhds hxT)
    have hFx : F x0 = cs.e z := by simp only [hF, Function.comp_apply, hx0, c0.e.left_inv hz]
    have hT' : IsOpen (cs.e.target ∩ cs.e.symm ⁻¹' c0.e.source) :=
      GlobalTheory.ChartGlue.isOpen_over cs.e c0.e.open_source
    have hF'd : DifferentiableAt ℂ F' (F x0) := hFx ▸
      (cs.holo_trans c0).differentiableAt (hT'.mem_nhds (GlobalTheory.ChartGlue.mem_over cs.e hzs hz))
    have hid : F' ∘ F =ᶠ[nhds x0] id := by
      filter_upwards [hTo.mem_nhds hxT] with v hv
      simp only [hF, hF', Function.comp_apply, id, cs.e.left_inv hv.2, c0.e.right_inv hv.1]
    have hcomp : HasFDerivAt id ((fderiv ℂ F' (F x0)).comp (fderiv ℂ F x0)) x0 :=
      (hF'd.hasFDerivAt.comp x0 hFd.hasFDerivAt).congr_of_eventuallyEq hid.symm
    have hone := hcomp.unique (hasFDerivAt_id x0)
    set w : V N := WithLp.toLp 2 ξ with hw
    have hwsum : w = ∑ j, ξ j • ReciprocityTheory.L2DbarEstimates.bas N j := by
      exact toLp_eq_sum_bas N ξ
    have hgw : ∀ a, fderiv ℂ (g a) x0 w = 0 := fun a => by
      have := hξ a
      simp only [ReciprocityTheory.L2DbarEstimates.wd_of_differentiableAt (hgD a)] at this
      rw [hwsum, map_sum]
      simpa [mul_comm] using this
    have hdF : fderiv ℂ F x0 w = 0 := by
      ext a
      have hFa : HasFDerivAt (fun v => (F v).ofLp a)
          ((EuclideanSpace.proj (𝕜 := ℂ) a).comp (fderiv ℂ F x0)) x0 :=
        (EuclideanSpace.proj (𝕜 := ℂ) a).hasFDerivAt.comp x0 hFd.hasFDerivAt
      have heq : (fun v => (F v).ofLp a) =ᶠ[nhds x0] g (b.succAbove a) := by
        filter_upwards [hTo.mem_nhds hxT] with v hv
        exact h₂ _ hv.2 a
      have := (hFa.congr_of_eventuallyEq heq.symm).fderiv
      have h2 := hgw (b.succAbove a)
      rw [this] at h2
      simpa using h2
    have hw0 : w = 0 := by
      have := congrArg (fun L : V N →L[ℂ] V N => L w) hone
      simp only [ContinuousLinearMap.comp_apply, hdF, map_zero, ContinuousLinearMap.id_apply] at this
      exact this.symm
    funext j
    have := congrArg (fun u : V N => u.ofLp j) hw0
    simpa [hw] using this

end GlobalTheory.FubiniStudyChart

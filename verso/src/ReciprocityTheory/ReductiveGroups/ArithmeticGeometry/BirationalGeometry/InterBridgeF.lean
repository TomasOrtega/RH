import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}
  (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem maDensity_eq_maDens {D : ℕ} (φ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    maDensity φ z = ReciprocityTheory.AnForm.maDens φ z := rfl

/- English proof (translation)
Rewrite using `[Finset.prod_eq_single k0]`. Simplify using the standard rewrite rules. Introduce `k _ hk`. Simplify using `[Function.update_apply, hk]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ k0) h`.
-/
theorem prod_norm_update_zpow [DecidableEq K] (k0 : K) (v : ℂ) (a : K → ℤ) :
    ∏ k, ‖Function.update (fun _ => (1 : ℂ)) k0 v k‖ ^ a k = ‖v‖ ^ a k0 := by
  rw [Finset.prod_eq_single k0]
  · simp
  · intro k _ hk
    simp [Function.update_apply, hk]
  · intro h
    exact absurd (Finset.mem_univ k0) h

/- English proof (translation)
Take `⟨k0⟩` from `hP.1`. Establish `hPh : IsMultiHomogIdeal P` using `hP.2.1.2.1`. Use `set j := chartIdx R.A x with hjdef`. Establish `hj : x ∈ (R.A.chart j).source` using `Classical.choose_spec (R.A.cover x)`. Use `set u := R.A.chart j x with hudef`.

Establish `hsu : (R.A.chart j).symm u = x` using `(R.A.chart j).left_inv hj`. Establish `huU : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x` using `⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact R.mem_U x⟩`. Take `⟨hQa, hQd⟩` from `brGood R Ψ x hx j hj`. Use `set Q := brQ R Ψ ∘ (R.A.chart j).symm with hQdef`. Use `set Df := fderiv ℂ Q u with hDf`.

Establish `hdet : Df.det ≠ 0` using `hQd`. Use `set Ce := Df.toContinuousLinearEquivOfDetNeZero hdet with hCe`. Establish `hCe' : (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) = Df` using `ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero Df hdet`. Establish `hstrict : HasStrictFDerivAt Q (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) u`. Rewrite using `[hCe']`.

Conclude with `hQa.hasStrictFDerivAt`. Use `set F := hstrict.toOpenPartialHomeomorph Q with hF`. Establish `hFc : (F : (Fin e → ℂ) → (Fin e → ℂ)) = Q` using `hstrict.toOpenPartialHomeomorph_coe`. Establish `hus : u ∈ F.source` using `hstrict.mem_toOpenPartialHomeomorph_source`. Establish `hyt : Q u ∈ F.target` using `hstrict.image_mem_toOpenPartialHomeomorph_target`.

Establish `hσu : F.symm (Q u) = u`. Use `F.left_inv hus` as an intermediate fact. Rewrite `this` using `[hFc]`. Then use the resulting hypothesis. Establish `hy0 : Q u = brQ R Ψ x` using `by simp only [hQdef, Function.comp_apply, hsu]`. Establish `hσa : AnalyticAt ℂ F.symm (Q u)`.

Use `F.analyticAt_symm (i := Ce) hyt ?_ ?_` and prove the remaining obligations. Rewrite using `[hσu, hFc]`. Conclude with `hQa`. Rewrite using `[hσu, hFc, hCe']`. Establish `hσd : HasFDerivAt F.symm (Ce.symm : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) (Q u)`.

Use `F.hasFDerivAt_symm hyt ?_` and prove the remaining obligations. Rewrite using `[hσu, hFc, hCe']`. Conclude with `hQa.differentiableAt.hasFDerivAt`. Use `set γ₀ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun y' => R.lift x ((R.A.chart j).symm (F.symm y')) with hγ₀`. Establish `hγ₀a : AnalyticAt ℂ γ₀ (Q u)` using `(analyticAt_lift_chart R x j huU).comp_of_eq hσa hσu`.

Establish `hγ₀u : γ₀ (Q u) = R.lift x x` using `by simp only [hγ₀, hσu, hsu]`. Use `set ψ0 : (Fin e → ℂ) → ℂ := fun y' => Ψ (segre (γ₀ y')) 0 with hψ0`. Establish `hψ0a : AnalyticAt ℂ ψ0 (Q u)` using `analyticAt_pi_iff.mp ((analyticAt_segre_lift R Ψ x j huU).comp_of_eq hσa hσu) 0`. Establish `hψ0u : ψ0 (Q u) ≠ 0`. Simplify using `only [hψ0, hγ₀u]`.

Conclude with `projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx`. Use `set c : (Fin e → ℂ) → K → ℂ := fun y' => Function.update (fun _ => (1 : ℂ)) k0 (ψ0 y')⁻¹ with hcdef`. Establish `hc_ne : ∀ y', ψ0 y' ≠ 0 → ∀ k, c y' k ≠ 0`. Introduce `y' h k`. Distinguish the cases in `hk : k = k0`.

Substitute `hk` using the available equality. Simplify using `[hcdef, h]`. Simplify using `[hcdef, Function.update_of_ne hk]`. Establish `hca : ∀ k, AnalyticAt ℂ (fun y' => c y' k) (Q u)`. Introduce `k`.

Distinguish the cases in `hk : k = k0`. Substitute `hk` using the available equality. Simplify using `only [hcdef, Function.update_self]`. Conclude with `hψ0a.inv hψ0u`. Simplify using `only [hcdef, Function.update_of_ne hk]`.

Conclude with `analyticAt_const`. Use `set γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun y' => bsmul (c y') (γ₀ y') with hγdef`. Establish `hγa : AnalyticAt ℂ γ (Q u)` using `analyticAt_pi_iff.mpr fun p => (hca p.1).mul (analyticAt_pi_iff.mp hγ₀a p)`. Establish `hprod : ∀ y', ∏ k, c y' k = (ψ0 y')⁻¹` using `fun y' => by`. Simplify using `[hcdef, Finset.prod_update_of_mem (Finset.mem_univ k0)]`.

Establish `hseg : ∀ y', segre (γ y') = (ψ0 y')⁻¹ • segre (γ₀ y')` using `fun y' => by`. Rewrite using `[← hprod y']`. Conclude with `segre_smul (c y') (γ₀ y')`. Use `⟨γ, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy0, hseg]`.

Simplify using `only [hψ0, hγ₀u]`. Both sides reduce to the same expression. Rewrite using `[← hy0]`. Establish `hU : ∀ᶠ y' in 𝓝 (Q u), F.symm y' ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x` using `hσa.continuousAt.preimage_mem_nhds (by`. Rewrite using `[hσu]`.

Conclude with `((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds huU)`. Use `filter_upwards [hγa.eventually_analyticAt, hU, F.open_target.mem_nhds hyt, hψ0a.continuousAt.eventually_ne hψ0u] with y' ha hUy ht h0`. Use `⟨ha.differentiableAt, mcPts_smul hPh (c y') (hc_ne y' h0) (R.mem x _ hUy.2), ?_⟩` and prove the remaining obligations. Establish `hq : Q (F.symm y') = y'`. Use `F.right_inv ht` as an intermediate fact.

Rewrite `this` using `[hFc]`. Then use the resulting hypothesis. Rewrite `hq` using `[hQdef, Function.comp_apply, brQ_eq_local R Ψ hUy.2]`. Rewrite using `[hseg, map_smul]`. Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations.

Simplify using `only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero]`. Conclude with `inv_mul_cancel₀ h0`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ]`. Rewrite using `[← congrFun hq i, div_eq_inv_mul]`. Rewrite using `[← hy0]`.

Take `⟨a, ha, hsa, -⟩` from `hs`. Establish `hlog : logNorm A s (γ (Q u)) = logNorm A s (R.lift x x)` using `by show logNorm A s (bsmul (c (Q u)) (γ₀ (Q u))) = _`. Rewrite using `[logNorm_bsmul A ha hsa (hc_ne _ hψ0u), hγ₀u]`. Rewrite using `[hlog]`. Use `congr 1`.

Establish `hblk : ∀ k, ∃ i, γ₀ (Q u) ⟨k, i⟩ ≠ 0`. Rewrite using `[hγ₀u]`. Conclude with `(R.mem x x (R.mem_U x)).1`. Establish `hH : ∀ i, cxHessian (fun y' => pot L i (γ y')) (Q u) = cxHessian (fun y' => pot L i (γ₀ y')) (Q u)`. Introduce `i`.

Use `set G : (Fin e → ℂ) → ℂ := fun y' => ((-((L i).a k0 : ℝ) : ℝ) : ℂ) * Complex.log (ψ0 y' / ψ0 (Q u)) with hG`. Use `set C : ℝ := -(((L i).a k0 : ℝ) * Real.log ‖ψ0 (Q u)‖) with hC`. Establish `hGa : AnalyticAt ℂ G (Q u)`. Use `analyticAt_const.mul ((hψ0a.div analyticAt_const hψ0u).clog ?_)` and prove the remaining obligations. Use `show ψ0 (Q u) / ψ0 (Q u) ∈ Complex.slitPlane`.

Rewrite using `[div_self hψ0u]`. Conclude with `Complex.one_mem_slitPlane`. Establish `heq : (fun y' => pot L i (γ y')) =ᶠ[𝓝 (Q u)] fun y' => pot L i (γ₀ y') + (G y').re + C` using `by filter_upwards [hψ0a.continuousAt.eventually_ne hψ0u, hγ₀a.continuousAt.eventually (isOpen_blockNonzero.mem_nhds hblk)] with y' h0 hb`. Establish `hpos : 0 < (L i).h (γ₀ y')` using `(L i).pos _ hb`. Establish `hn0 : ‖(ψ0 y')⁻¹‖ ^ (L i).a k0 ≠ 0` using `zpow_ne_zero _ (norm_ne_zero_iff.mpr (inv_ne_zero h0))`.

Simplify using `only [pot, hγdef]`. Rewrite using `[show bsmul (c y') (γ₀ y') = fun p => c y' p.1 * γ₀ y' p from rfl, (L i).smul _ _ (hc_ne y' h0), prod_norm_update_zpow, Real.log_mul hn0 hpos.ne', hG, hC, Complex.re_ofReal_mul, Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.mpr h0) (norm_ne_zero_iff.mpr hψ0u), Real.log …`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[cxHessian_congr heq, cxHessian_add_re (φ := fun y' => pot L i (γ₀ y')) C (pot_contDiffAt (hL i) hγ₀a hblk) hGa]`. Establish `hmd : maDensity (fun i y' => pot L i (γ y')) (Q u) = maDensity (fun i y' => pot L i (γ₀ y')) (Q u)`.

Simplify using `only [maDensity, hH]`. Rewrite using `[hmd, maDensity_eq_maDens]`. Establish `hcd : ∀ i, ContDiffAt ℝ 2 (fun v => pot L i (R.lift x ((R.A.chart j).symm v))) (F.symm (Q u))`. Introduce `i`. Rewrite using `[hσu]`.

Conclude with `pot_contDiffAt (hL i) (analyticAt_lift_chart R x j huU) (by rw [hsu]; exact (R.mem x x (R.mem_U x)).1)`. Establish `hcomp : ReciprocityTheory.AnForm.maDens (fun i y' => pot L i (γ₀ y')) (Q u) = ReciprocityTheory.AnForm.maDens (fun i v => pot L i (R.lift x ((R.A.chart j).symm v))) (F.symm (Q u)) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC F.symm (Q u)).det` using `ReciprocityTheory.AnForm.A.maDens_comp (fun i v => pot L i (R.lift x ((R.A.chart j).symm v))) F.symm (Q u) hσa hcd`. Establish `hdetinv : LinearMap.det ((Ce.symm : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = (LinearMap.det (Df : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)))⁻¹`. Use `ContinuousLinearEquiv.det_coe_symm Ce` as an intermediate fact. Rewrite `this` using `[hCe']`.

Conclude with `this`. Establish `hloc : ReciprocityTheory.AnForm.maDens (fun i v => pot L i (R.lift x ((R.A.chart j).symm v))) u = locDens R.A (fun i => potOf R (L i)) j u`. Unfold `locDens`. Rewrite using `[hsu]`. Both sides reduce to the same expression.

Rewrite using `[hcomp, hσu, ReciprocityTheory.AnForm.A.det_jacC, hσd.fderiv, hdetinv, hloc, Complex.normSq_inv, Complex.normSq_eq_norm_sq]`. Unfold `pushDens`. Rewrite using `[div_eq_mul_inv]`.
-/
theorem exists_sheet_brW (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι)
    (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (hs : IsSectionOn P A s)
    (x : R.X) (hx : x ∉ brBad R Ψ) :
    ∃ γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ, IsSheet P Ψ (brQ R Ψ x) (brW R Ψ x) γ ∧
      logNorm A s (γ (brQ R Ψ x)) * maDensity (fun j y' => pot L j (γ y')) (brQ R Ψ x) =
        logNorm A s (R.lift x x) * pushDens R.A (fun j => potOf R (L j)) (brQ R Ψ) x := by
  classical
  obtain ⟨k0⟩ := hP.1
  have hPh : IsMultiHomogIdeal P := hP.2.1.2.1
  set j := chartIdx R.A x with hjdef
  have hj : x ∈ (R.A.chart j).source := Classical.choose_spec (R.A.cover x)
  set u := R.A.chart j x with hudef
  have hsu : (R.A.chart j).symm u = x := (R.A.chart j).left_inv hj
  have huU : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact R.mem_U x⟩
  obtain ⟨hQa, hQd⟩ := brGood R Ψ x hx j hj
  set Q := brQ R Ψ ∘ (R.A.chart j).symm with hQdef
  set Df := fderiv ℂ Q u with hDf
  have hdet : Df.det ≠ 0 := hQd
  set Ce := Df.toContinuousLinearEquivOfDetNeZero hdet with hCe
  have hCe' : (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) = Df :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero Df hdet
  have hstrict : HasStrictFDerivAt Q (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) u := by
    rw [hCe']; exact hQa.hasStrictFDerivAt
  set F := hstrict.toOpenPartialHomeomorph Q with hF
  have hFc : (F : (Fin e → ℂ) → (Fin e → ℂ)) = Q := hstrict.toOpenPartialHomeomorph_coe
  have hus : u ∈ F.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hyt : Q u ∈ F.target := hstrict.image_mem_toOpenPartialHomeomorph_target
  have hσu : F.symm (Q u) = u := by
    have := F.left_inv hus
    rwa [hFc] at this
  have hy0 : Q u = brQ R Ψ x := by simp only [hQdef, Function.comp_apply, hsu]
  have hσa : AnalyticAt ℂ F.symm (Q u) := by
    refine F.analyticAt_symm (i := Ce) hyt ?_ ?_
    · rw [hσu, hFc]; exact hQa
    · rw [hσu, hFc, hCe']
  have hσd : HasFDerivAt F.symm (Ce.symm : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) (Q u) := by
    refine F.hasFDerivAt_symm hyt ?_
    rw [hσu, hFc, hCe']
    exact hQa.differentiableAt.hasFDerivAt
  set γ₀ : (Fin e → ℂ) → (Σ k, ι k) → ℂ :=
    fun y' => R.lift x ((R.A.chart j).symm (F.symm y')) with hγ₀
  have hγ₀a : AnalyticAt ℂ γ₀ (Q u) := (analyticAt_lift_chart R x j huU).comp_of_eq hσa hσu
  have hγ₀u : γ₀ (Q u) = R.lift x x := by simp only [hγ₀, hσu, hsu]
  set ψ0 : (Fin e → ℂ) → ℂ := fun y' => Ψ (segre (γ₀ y')) 0 with hψ0
  have hψ0a : AnalyticAt ℂ ψ0 (Q u) :=
    analyticAt_pi_iff.mp ((analyticAt_segre_lift R Ψ x j huU).comp_of_eq hσa hσu) 0
  have hψ0u : ψ0 (Q u) ≠ 0 := by
    simp only [hψ0, hγ₀u]; exact projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx
  set c : (Fin e → ℂ) → K → ℂ := fun y' => Function.update (fun _ => (1 : ℂ)) k0 (ψ0 y')⁻¹
    with hcdef
  have hc_ne : ∀ y', ψ0 y' ≠ 0 → ∀ k, c y' k ≠ 0 := by
    intro y' h k
    by_cases hk : k = k0
    · subst hk; simp [hcdef, h]
    · simp [hcdef, Function.update_of_ne hk]
  have hca : ∀ k, AnalyticAt ℂ (fun y' => c y' k) (Q u) := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp only [hcdef, Function.update_self]; exact hψ0a.inv hψ0u
    · simp only [hcdef, Function.update_of_ne hk]; exact analyticAt_const
  set γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun y' => bsmul (c y') (γ₀ y') with hγdef
  have hγa : AnalyticAt ℂ γ (Q u) :=
    analyticAt_pi_iff.mpr fun p => (hca p.1).mul (analyticAt_pi_iff.mp hγ₀a p)
  have hprod : ∀ y', ∏ k, c y' k = (ψ0 y')⁻¹ := fun y' => by
    simp [hcdef, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  have hseg : ∀ y', segre (γ y') = (ψ0 y')⁻¹ • segre (γ₀ y') := fun y' => by
    rw [← hprod y']; exact segre_smul (c y') (γ₀ y')
  refine ⟨γ, ⟨?_, ?_⟩, ?_⟩
  · rw [← hy0, hseg]
    simp only [hψ0, hγ₀u]
    rfl
  · rw [← hy0]
    have hU : ∀ᶠ y' in 𝓝 (Q u),
        F.symm y' ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
      hσa.continuousAt.preimage_mem_nhds (by
        rw [hσu]; exact ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds huU)
    filter_upwards [hγa.eventually_analyticAt, hU, F.open_target.mem_nhds hyt,
      hψ0a.continuousAt.eventually_ne hψ0u] with y' ha hUy ht h0
    refine ⟨ha.differentiableAt, mcPts_smul hPh (c y') (hc_ne y' h0) (R.mem x _ hUy.2), ?_⟩
    have hq : Q (F.symm y') = y' := by
      have := F.right_inv ht
      rwa [hFc] at this
    rw [hQdef, Function.comp_apply, brQ_eq_local R Ψ hUy.2] at hq
    rw [hseg, map_smul]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero]
      exact inv_mul_cancel₀ h0
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
      rw [← congrFun hq i, div_eq_inv_mul]
  · rw [← hy0]
    obtain ⟨a, ha, hsa, -⟩ := hs
    have hlog : logNorm A s (γ (Q u)) = logNorm A s (R.lift x x) := by
      show logNorm A s (bsmul (c (Q u)) (γ₀ (Q u))) = _
      rw [logNorm_bsmul A ha hsa (hc_ne _ hψ0u), hγ₀u]
    rw [hlog]
    congr 1
    have hblk : ∀ k, ∃ i, γ₀ (Q u) ⟨k, i⟩ ≠ 0 := by
      rw [hγ₀u]; exact (R.mem x x (R.mem_U x)).1
    have hH : ∀ i, cxHessian (fun y' => pot L i (γ y')) (Q u) =
        cxHessian (fun y' => pot L i (γ₀ y')) (Q u) := by
      intro i
      set G : (Fin e → ℂ) → ℂ :=
        fun y' => ((-((L i).a k0 : ℝ) : ℝ) : ℂ) * Complex.log (ψ0 y' / ψ0 (Q u)) with hG
      set C : ℝ := -(((L i).a k0 : ℝ) * Real.log ‖ψ0 (Q u)‖) with hC
      have hGa : AnalyticAt ℂ G (Q u) := by
        refine analyticAt_const.mul ((hψ0a.div analyticAt_const hψ0u).clog ?_)
        show ψ0 (Q u) / ψ0 (Q u) ∈ Complex.slitPlane
        rw [div_self hψ0u]
        exact Complex.one_mem_slitPlane
      have heq : (fun y' => pot L i (γ y')) =ᶠ[𝓝 (Q u)]
          fun y' => pot L i (γ₀ y') + (G y').re + C := by
        filter_upwards [hψ0a.continuousAt.eventually_ne hψ0u,
          hγ₀a.continuousAt.eventually (isOpen_blockNonzero.mem_nhds hblk)] with y' h0 hb
        have hpos : 0 < (L i).h (γ₀ y') := (L i).pos _ hb
        have hn0 : ‖(ψ0 y')⁻¹‖ ^ (L i).a k0 ≠ 0 :=
          zpow_ne_zero _ (norm_ne_zero_iff.mpr (inv_ne_zero h0))
        simp only [pot, hγdef]
        rw [show bsmul (c y') (γ₀ y') = fun p => c y' p.1 * γ₀ y' p from rfl, (L i).smul _ _ (hc_ne y' h0), prod_norm_update_zpow, Real.log_mul hn0 hpos.ne',
          hG, hC, Complex.re_ofReal_mul, Complex.log_re, norm_div,
          Real.log_div (norm_ne_zero_iff.mpr h0) (norm_ne_zero_iff.mpr hψ0u), Real.log_zpow,
          norm_inv, Real.log_inv]
        ring
      rw [cxHessian_congr heq, cxHessian_add_re (φ := fun y' => pot L i (γ₀ y')) C
        (pot_contDiffAt (hL i) hγ₀a hblk) hGa]
    have hmd : maDensity (fun i y' => pot L i (γ y')) (Q u) =
        maDensity (fun i y' => pot L i (γ₀ y')) (Q u) := by
      simp only [maDensity, hH]
    rw [hmd, maDensity_eq_maDens]
    have hcd : ∀ i, ContDiffAt ℝ 2 (fun v => pot L i (R.lift x ((R.A.chart j).symm v)))
        (F.symm (Q u)) := by
      intro i
      rw [hσu]
      exact pot_contDiffAt (hL i) (analyticAt_lift_chart R x j huU)
        (by rw [hsu]; exact (R.mem x x (R.mem_U x)).1)
    have hcomp : ReciprocityTheory.AnForm.maDens (fun i y' => pot L i (γ₀ y')) (Q u) =
        ReciprocityTheory.AnForm.maDens (fun i v => pot L i (R.lift x ((R.A.chart j).symm v)))
          (F.symm (Q u)) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC F.symm (Q u)).det :=
      ReciprocityTheory.AnForm.A.maDens_comp (fun i v => pot L i (R.lift x ((R.A.chart j).symm v)))
        F.symm (Q u) hσa hcd
    have hdetinv : LinearMap.det ((Ce.symm : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = (LinearMap.det (Df : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)))⁻¹ := by
      have := ContinuousLinearEquiv.det_coe_symm Ce
      rw [hCe'] at this
      exact this
    have hloc : ReciprocityTheory.AnForm.maDens (fun i v => pot L i (R.lift x ((R.A.chart j).symm v))) u =
        locDens R.A (fun i => potOf R (L i)) j u := by
      unfold locDens
      rw [hsu]
      rfl
    rw [hcomp, hσu, ReciprocityTheory.AnForm.A.det_jacC, hσd.fderiv, hdetinv, hloc, Complex.normSq_inv,
      Complex.normSq_eq_norm_sq]
    unfold pushDens
    rw [div_eq_mul_inv]

end ReciprocityTheory.ChartRestriction.G.Geo

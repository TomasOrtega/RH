import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StChartVelLift
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StProjHoloLocal
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.MCoordIdealGenericPointEq
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simpa using hasDerivAt_const t a`. Consider the case `add p q hp hq`. Establish `hf : (fun s => eval (γ s) (p + q)) = fun s => eval (γ s) p + eval (γ s) q`. Use function extensionality and compare the values at `s`.

Simplify using the standard rewrite rules. Rewrite using `[hf]`. Use `(hp.add hq).congr_deriv ?_` and prove the remaining obligations. Simplify using `only [map_add, add_mul, Finset.sum_add_distrib]`. Consider the case `mul_X p n hp`.

Establish `hn : HasDerivAt (fun s => γ s n) (w n) t` using `hasDerivAt_pi.1 hγ n`. Establish `hf : (fun s => eval (γ s) (p * X n)) = fun s => eval (γ s) p * γ s n`. Use function extensionality and compare the values at `s`. Simplify using the standard rewrite rules. Rewrite using `[hf]`.

Use `(hp.mul hn).congr_deriv ?_` and prove the remaining obligations. Establish `hs : ∑ i, eval (γ t) (pderiv i (p * X n)) * w i = ∑ i, eval (γ t) (pderiv i p) * w i * γ t n + ∑ i, eval (γ t) p * ((Pi.single n (1 : ℂ) : σ → ℂ) i * w i)`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, eval_X]`.

Distinguish the cases in `h : i = n`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using `[h, Ne.symm h]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hs, ← Finset.mul_sum, ← Finset.sum_mul]`. Use `congr 2`. Simplify using `[Pi.single_apply]`.
-/
theorem hasDerivAt_eval_comp {σ : Type*} [Fintype σ] (f : MvPolynomial σ ℂ) {γ : ℂ → σ → ℂ} {w : σ → ℂ} {t : ℂ}
    (hγ : HasDerivAt γ w t) :
    HasDerivAt (fun s => eval (γ s) f) (∑ i, eval (γ t) (pderiv i f) * w i) t := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const t a
  | add p q hp hq =>
    have hf : (fun s => eval (γ s) (p + q)) = fun s => eval (γ s) p + eval (γ s) q := by
      funext s
      simp
    rw [hf]
    refine (hp.add hq).congr_deriv ?_
    simp only [map_add, add_mul, Finset.sum_add_distrib]
  | mul_X p n hp =>
    have hn : HasDerivAt (fun s => γ s n) (w n) t := hasDerivAt_pi.1 hγ n
    have hf : (fun s => eval (γ s) (p * X n)) = fun s => eval (γ s) p * γ s n := by
      funext s
      simp
    rw [hf]
    refine (hp.mul hn).congr_deriv ?_
    have hs : ∑ i, eval (γ t) (pderiv i (p * X n)) * w i =
        ∑ i, eval (γ t) (pderiv i p) * w i * γ t n + ∑ i, eval (γ t) p * ((Pi.single n (1 : ℂ) : σ → ℂ) i * w i) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, eval_X]
      by_cases h : i = n
      · subst h
        simp
        ring
      · simp [h, Ne.symm h]
        ring
    rw [hs, ← Finset.mul_sum, ← Finset.sum_mul]
    congr 2
    simp [Pi.single_apply]

/- English proof (translation)
Introduce `II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X k y hy v hv`. Establish `hcompat : ReciprocityTheory.AnForm.M.IsCompatChart X.M.atlas (X.S.R.chart k)` using `X.S.R.compat k`. Establish `hx : (X.S.R.chart k).symm y ∈ (X.S.R.chart k).source` using `(X.S.R.chart k).map_target hy`. Take `⟨U, hUo, hxU, s, hs, hshol⟩` from `X.M.sections ((X.S.R.chart k).symm y)`. Take `⟨j, hj⟩` from `X.M.atlas.cover ((X.S.R.chart k).symm y)`.

Use `set V : Set (Fin D.n → ℂ) := (X.S.R.chart k).target ∩ (X.S.R.chart k).symm ⁻¹' (U ∩ (X.M.atlas.chart j).source) with hV`. Establish `hVo : IsOpen V` using `(X.S.R.chart k).continuousOn_symm.isOpen_inter_preimage (X.S.R.chart k).open_target (hUo.inter (X.M.atlas.chart j).open_source)`. Establish `hanal : ∀ u ∈ V, ∀ p, AnalyticAt ℂ (fun u => s ((X.S.R.chart k).symm u) p) u`. Introduce `u hu p`. Establish `h1 : AnalyticAt ℂ (X.M.atlas.chart j ∘ (X.S.R.chart k).symm) u` using `(hcompat j).2 u ⟨hu.1, hu.2.2⟩`.

Establish `h2 : AnalyticAt ℂ ((fun y' => s y' p) ∘ (X.M.atlas.chart j).symm) ((X.M.atlas.chart j ∘ (X.S.R.chart k).symm) u)`. Use `hshol p j _ ⟨(X.M.atlas.chart j).map_source hu.2.2, ?_⟩` and prove the remaining obligations. Use `show (X.M.atlas.chart j).symm ((X.M.atlas.chart j) ((X.S.R.chart k).symm u)) ∈ U`. Rewrite using `[(X.M.atlas.chart j).left_inv hu.2.2]`. Conclude with `hu.2.1`.

Use `(h2.comp h1).congr ?_` and prove the remaining obligations. Use `filter_upwards [hVo.mem_nhds hu] with u' hu'`. Simplify using `only [Function.comp_apply]`. Rewrite using `[(X.M.atlas.chart j).left_inv hu'.2.2]`. Use `set L : ℂ → Fin D.n → ℂ := fun σ => y + σ • v with hL`.

Establish `hLd : ∀ σ, HasDerivAt L v σ` using `fun σ => by`. Establish `h` using `((hasDerivAt_id σ).smul_const v).const_add y`. Simplify using `only [id, one_smul] at h`. Conclude with `h`. Establish `hL0 : L 0 = y` using `by simp [hL]`.

Use `set T : Set ℂ := L ⁻¹' V with hT`. Establish `hTo : IsOpen T` using `hVo.preimage (continuous_const.add (continuous_id.smul continuous_const))`. Establish `hT0 : (0 : ℂ) ∈ T` using `by show L 0 ∈ V`. Rewrite using `[hL0]`. Conclude with `⟨hy, hxU, hj⟩`.

Use `set γ : ℂ → (Σ k, ι k) → ℂ := fun σ => s ((X.S.R.chart k).symm (L σ)) with hγdef`. Establish `hγd : ∀ σ ∈ T, DifferentiableAt ℂ γ σ` using `fun σ hσ => differentiableAt_pi.2 fun p => (hanal (L σ) hσ p).differentiableAt.comp σ (hLd σ).differentiableAt`. Establish `hγmem : ∀ σ ∈ T, γ σ ∈ mcPts (mCoordIdeal D.y) ∧ X.M.proj (γ σ) = (X.S.R.chart k).symm (L σ)` using `fun σ hσ => hs _ hσ.2.1`. Establish `hγ0 : γ 0 = s ((X.S.R.chart k).symm y)` using `by simp [hγdef, hL0]`. Establish `hγw : HasDerivAt γ (deriv γ 0) 0` using `(hγd 0 hT0).hasDerivAt`.

Establish `hTn : T ∈ 𝓝 (0 : ℂ)` using `hTo.mem_nhds hT0`. Establish `hline : (fun σ => X.S.R.chart k (X.M.proj (γ σ))) =ᶠ[𝓝 0] L` using `by filter_upwards [hTn] with σ hσ`. Rewrite using `[(hγmem σ hσ).2, (X.S.R.chart k).right_inv hσ.1]`. Establish `hz : γ 0 ∈ mcPts (mCoordIdeal D.y)` using `(hγmem 0 hT0).1`. Establish `hpz : X.M.proj (γ 0) = (X.S.R.chart k).symm y` using `by rw [(hγmem 0 hT0).2, hL0]`.

Use `⟨γ 0, hz, hpz, deriv γ 0, ⟨γ, rfl, hγw, ?_, (hLd 0).congr_of_eventuallyEq hline⟩, ?_, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hTn] with σ hσ`. Conclude with `⟨hγd σ hσ, (hγmem σ hσ).1⟩`. Introduce `f hf`. Establish `hder` using `hasDerivAt_eval_comp (map (Int.castRingHom ℂ) f) hγw`.

Establish `hzero : (fun σ => eval (γ σ) (map (Int.castRingHom ℂ) f)) =ᶠ[𝓝 0] fun _ => (0 : ℂ)` using `by filter_upwards [hTn] with σ hσ`. Conclude with `(hγmem σ hσ).1.2 f hf`. Conclude with `hder.unique ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hzero)`. Introduce `c hwc`. Take `⟨W, hWo, hzW, F, hFd, hF⟩` from `hP II Ψ K ι Ω E D X.M (X.S.R.chart k) hcompat (γ 0) hz (by rw [hpz]; exact hx)`.

Establish `hFz : HasFDerivAt F (fderiv ℂ F (γ 0)) (γ 0)` using `(hFd.differentiableAt (hWo.mem_nhds hzW)).hasFDerivAt`. Establish `hWγ : ∀ᶠ σ in 𝓝 (0 : ℂ), γ σ ∈ W` using `hγw.continuousAt.preimage_mem_nhds (hWo.mem_nhds hzW)`. Establish `h1 : fderiv ℂ F (γ 0) (deriv γ 0) = v`. Use `(hFz.comp_hasDerivAt (0 : ℂ) hγw).unique ((hLd 0).congr_of_eventuallyEq ?_)` and prove the remaining obligations. Use `filter_upwards [hTn, hWγ, hline] with σ hσ hσW hσl`.

Rewrite using `[Function.comp_apply, ← (hF (γ σ) ⟨hσW, (hγmem σ hσ).1⟩).2]`. Conclude with `hσl`. Use `set δ : ℂ → (Σ k, ι k) → ℂ := fun σ => torusSmul (fun k => Complex.exp (σ * c k)) (γ 0) with hδ`. Establish `hδ0 : δ 0 = γ 0`. Use function extensionality and compare the values at `p`.

Simplify using `[hδ, torusSmul]`. Establish `hδd : HasDerivAt δ (torusSmul c (γ 0)) 0`. Use `hasDerivAt_pi.2 fun p => ?_` and prove the remaining obligations. Establish `h` using `(((hasDerivAt_id (0 : ℂ)).mul_const (c p.1)).cexp).mul_const (γ 0 p)`. Simplify `h` using `[hδ, torusSmul]`.

Establish `hδmem : ∀ σ, δ σ ∈ mcPts (mCoordIdeal D.y)` using `fun σ => ComponentDataEquivalence.mcPts_torus D.arith.2.1.2.1 hz fun k => Complex.exp_ne_zero _`. Establish `hδproj : ∀ σ, X.M.proj (δ σ) = X.M.proj (γ 0)` using `fun σ => ((X.M.fibre (γ 0) hz (δ σ) (hδmem σ)).2 ⟨_, fun k => Complex.exp_ne_zero _, rfl⟩).symm`. Establish `hWδ : ∀ᶠ σ in 𝓝 (0 : ℂ), δ σ ∈ W`. Use `hδd.continuousAt.preimage_mem_nhds (hWo.mem_nhds (hδ0 ▸ hzW))` as an intermediate fact. Conclude with `this`.

Establish `h2 : fderiv ℂ F (γ 0) (torusSmul c (γ 0)) = 0`. Establish `hFz' : HasFDerivAt F (fderiv ℂ F (γ 0)) (δ 0)` using `hδ0 ▸ hFz`. Use `(hFz'.comp_hasDerivAt (0 : ℂ) hδd).unique ((hasDerivAt_const (0 : ℂ) (X.S.R.chart k (X.M.proj (γ 0)))).congr_of_eventuallyEq ?_)` and prove the remaining obligations. Use `filter_upwards [hWδ] with σ hσW`. Rewrite using `[Function.comp_apply, ← (hF (δ σ) ⟨hσW, hδmem σ⟩).2, hδproj σ]`.

Conclude with `hv (h1.symm.trans (hwc ▸ h2))`.
-/
theorem ChartVelLift.proof (hP : ProjHoloLocal.Statement) : ChartVelLift.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X k y hy v hv
  classical
  have hcompat : ReciprocityTheory.AnForm.M.IsCompatChart X.M.atlas (X.S.R.chart k) := X.S.R.compat k
  have hx : (X.S.R.chart k).symm y ∈ (X.S.R.chart k).source := (X.S.R.chart k).map_target hy
  obtain ⟨U, hUo, hxU, s, hs, hshol⟩ := X.M.sections ((X.S.R.chart k).symm y)
  obtain ⟨j, hj⟩ := X.M.atlas.cover ((X.S.R.chart k).symm y)

  set V : Set (Fin D.n → ℂ) := (X.S.R.chart k).target ∩
    (X.S.R.chart k).symm ⁻¹' (U ∩ (X.M.atlas.chart j).source) with hV
  have hVo : IsOpen V := (X.S.R.chart k).continuousOn_symm.isOpen_inter_preimage (X.S.R.chart k).open_target
    (hUo.inter (X.M.atlas.chart j).open_source)

  have hanal : ∀ u ∈ V, ∀ p, AnalyticAt ℂ (fun u => s ((X.S.R.chart k).symm u) p) u := by
    intro u hu p
    have h1 : AnalyticAt ℂ (X.M.atlas.chart j ∘ (X.S.R.chart k).symm) u :=
      (hcompat j).2 u ⟨hu.1, hu.2.2⟩
    have h2 : AnalyticAt ℂ ((fun y' => s y' p) ∘ (X.M.atlas.chart j).symm)
        ((X.M.atlas.chart j ∘ (X.S.R.chart k).symm) u) := by
      refine hshol p j _ ⟨(X.M.atlas.chart j).map_source hu.2.2, ?_⟩
      show (X.M.atlas.chart j).symm ((X.M.atlas.chart j) ((X.S.R.chart k).symm u)) ∈ U
      rw [(X.M.atlas.chart j).left_inv hu.2.2]
      exact hu.2.1
    refine (h2.comp h1).congr ?_
    filter_upwards [hVo.mem_nhds hu] with u' hu'
    simp only [Function.comp_apply]
    rw [(X.M.atlas.chart j).left_inv hu'.2.2]

  set L : ℂ → Fin D.n → ℂ := fun σ => y + σ • v with hL
  have hLd : ∀ σ, HasDerivAt L v σ := fun σ => by
    have h := ((hasDerivAt_id σ).smul_const v).const_add y
    simp only [id, one_smul] at h
    exact h
  have hL0 : L 0 = y := by simp [hL]
  set T : Set ℂ := L ⁻¹' V with hT
  have hTo : IsOpen T := hVo.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have hT0 : (0 : ℂ) ∈ T := by
    show L 0 ∈ V
    rw [hL0]
    exact ⟨hy, hxU, hj⟩
  set γ : ℂ → (Σ k, ι k) → ℂ := fun σ => s ((X.S.R.chart k).symm (L σ)) with hγdef
  have hγd : ∀ σ ∈ T, DifferentiableAt ℂ γ σ := fun σ hσ =>
    differentiableAt_pi.2 fun p => (hanal (L σ) hσ p).differentiableAt.comp σ (hLd σ).differentiableAt
  have hγmem : ∀ σ ∈ T, γ σ ∈ mcPts (mCoordIdeal D.y) ∧
      X.M.proj (γ σ) = (X.S.R.chart k).symm (L σ) := fun σ hσ => hs _ hσ.2.1
  have hγ0 : γ 0 = s ((X.S.R.chart k).symm y) := by simp [hγdef, hL0]
  have hγw : HasDerivAt γ (deriv γ 0) 0 := (hγd 0 hT0).hasDerivAt
  have hTn : T ∈ 𝓝 (0 : ℂ) := hTo.mem_nhds hT0

  have hline : (fun σ => X.S.R.chart k (X.M.proj (γ σ))) =ᶠ[𝓝 0] L := by
    filter_upwards [hTn] with σ hσ
    rw [(hγmem σ hσ).2, (X.S.R.chart k).right_inv hσ.1]
  have hz : γ 0 ∈ mcPts (mCoordIdeal D.y) := (hγmem 0 hT0).1
  have hpz : X.M.proj (γ 0) = (X.S.R.chart k).symm y := by rw [(hγmem 0 hT0).2, hL0]
  refine ⟨γ 0, hz, hpz, deriv γ 0, ⟨γ, rfl, hγw, ?_, (hLd 0).congr_of_eventuallyEq hline⟩, ?_, ?_⟩
  · filter_upwards [hTn] with σ hσ
    exact ⟨hγd σ hσ, (hγmem σ hσ).1⟩
  ·
    intro f hf
    have hder := hasDerivAt_eval_comp (map (Int.castRingHom ℂ) f) hγw
    have hzero : (fun σ => eval (γ σ) (map (Int.castRingHom ℂ) f)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      filter_upwards [hTn] with σ hσ
      exact (hγmem σ hσ).1.2 f hf
    exact hder.unique ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hzero)
  ·
    intro c hwc
    obtain ⟨W, hWo, hzW, F, hFd, hF⟩ :=
      hP II Ψ K ι Ω E D X.M (X.S.R.chart k) hcompat (γ 0) hz (by rw [hpz]; exact hx)
    have hFz : HasFDerivAt F (fderiv ℂ F (γ 0)) (γ 0) :=
      (hFd.differentiableAt (hWo.mem_nhds hzW)).hasFDerivAt

    have hWγ : ∀ᶠ σ in 𝓝 (0 : ℂ), γ σ ∈ W := hγw.continuousAt.preimage_mem_nhds (hWo.mem_nhds hzW)
    have h1 : fderiv ℂ F (γ 0) (deriv γ 0) = v := by
      refine (hFz.comp_hasDerivAt (0 : ℂ) hγw).unique ((hLd 0).congr_of_eventuallyEq ?_)
      filter_upwards [hTn, hWγ, hline] with σ hσ hσW hσl
      rw [Function.comp_apply, ← (hF (γ σ) ⟨hσW, (hγmem σ hσ).1⟩).2]
      exact hσl

    set δ : ℂ → (Σ k, ι k) → ℂ := fun σ => torusSmul (fun k => Complex.exp (σ * c k)) (γ 0) with hδ
    have hδ0 : δ 0 = γ 0 := by
      funext p
      simp [hδ, torusSmul]
    have hδd : HasDerivAt δ (torusSmul c (γ 0)) 0 := by
      refine hasDerivAt_pi.2 fun p => ?_
      have h := (((hasDerivAt_id (0 : ℂ)).mul_const (c p.1)).cexp).mul_const (γ 0 p)
      simpa [hδ, torusSmul] using h
    have hδmem : ∀ σ, δ σ ∈ mcPts (mCoordIdeal D.y) := fun σ =>
      ComponentDataEquivalence.mcPts_torus D.arith.2.1.2.1 hz fun k => Complex.exp_ne_zero _
    have hδproj : ∀ σ, X.M.proj (δ σ) = X.M.proj (γ 0) := fun σ =>
      ((X.M.fibre (γ 0) hz (δ σ) (hδmem σ)).2 ⟨_, fun k => Complex.exp_ne_zero _, rfl⟩).symm
    have hWδ : ∀ᶠ σ in 𝓝 (0 : ℂ), δ σ ∈ W := by
      have := hδd.continuousAt.preimage_mem_nhds (hWo.mem_nhds (hδ0 ▸ hzW))
      exact this
    have h2 : fderiv ℂ F (γ 0) (torusSmul c (γ 0)) = 0 := by
      have hFz' : HasFDerivAt F (fderiv ℂ F (γ 0)) (δ 0) := hδ0 ▸ hFz
      refine (hFz'.comp_hasDerivAt (0 : ℂ) hδd).unique
        ((hasDerivAt_const (0 : ℂ) (X.S.R.chart k (X.M.proj (γ 0)))).congr_of_eventuallyEq ?_)
      filter_upwards [hWδ] with σ hσW
      rw [Function.comp_apply, ← (hF (δ σ) ⟨hσW, hδmem σ⟩).2, hδproj σ]
    exact hv (h1.symm.trans (hwc ▸ h2))

end GroundTheory.Heights₂.Heights.LowerBoundFree

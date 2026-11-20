import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StChartVelLiftCharts
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PChartVelLift
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GroundTheory.Heights₂.Heights.LowerBoundFree

/- English proof (translation)
Introduce `II Ψ _ K _ ι _ Ω _ _ E _ _ D M C k y hy v hv`. Establish `hcompat : ReciprocityTheory.AnForm.M.IsCompatChart M.atlas (C.chart k)` using `C.compat k`. Establish `hx : (C.chart k).symm y ∈ (C.chart k).source` using `(C.chart k).map_target hy`. Take `⟨U, hUo, hxU, s, hs, hshol⟩` from `M.sections ((C.chart k).symm y)`. Take `⟨j, hj⟩` from `M.atlas.cover ((C.chart k).symm y)`.

Use `set V : Set (Fin D.n → ℂ) := (C.chart k).target ∩ (C.chart k).symm ⁻¹' (U ∩ (M.atlas.chart j).source) with hV`. Establish `hVo : IsOpen V` using `(C.chart k).continuousOn_symm.isOpen_inter_preimage (C.chart k).open_target (hUo.inter (M.atlas.chart j).open_source)`. Establish `hanal : ∀ u ∈ V, ∀ p, AnalyticAt ℂ (fun u => s ((C.chart k).symm u) p) u`. Introduce `u hu p`. Establish `h1 : AnalyticAt ℂ (M.atlas.chart j ∘ (C.chart k).symm) u` using `(hcompat j).2 u ⟨hu.1, hu.2.2⟩`.

Establish `h2 : AnalyticAt ℂ ((fun y' => s y' p) ∘ (M.atlas.chart j).symm) ((M.atlas.chart j ∘ (C.chart k).symm) u)`. Use `hshol p j _ ⟨(M.atlas.chart j).map_source hu.2.2, ?_⟩` and prove the remaining obligations. Use `show (M.atlas.chart j).symm ((M.atlas.chart j) ((C.chart k).symm u)) ∈ U`. Rewrite using `[(M.atlas.chart j).left_inv hu.2.2]`. Conclude with `hu.2.1`.

Use `(h2.comp h1).congr ?_` and prove the remaining obligations. Use `filter_upwards [hVo.mem_nhds hu] with u' hu'`. Simplify using `only [Function.comp_apply]`. Rewrite using `[(M.atlas.chart j).left_inv hu'.2.2]`. Use `set L : ℂ → Fin D.n → ℂ := fun σ => y + σ • v with hL`.

Establish `hLd : ∀ σ, HasDerivAt L v σ` using `fun σ => by`. Establish `h` using `((hasDerivAt_id σ).smul_const v).const_add y`. Simplify using `only [id, one_smul] at h`. Conclude with `h`. Establish `hL0 : L 0 = y` using `by simp [hL]`.

Use `set T : Set ℂ := L ⁻¹' V with hT`. Establish `hTo : IsOpen T` using `hVo.preimage (continuous_const.add (continuous_id.smul continuous_const))`. Establish `hT0 : (0 : ℂ) ∈ T` using `by show L 0 ∈ V`. Rewrite using `[hL0]`. Conclude with `⟨hy, hxU, hj⟩`.

Use `set γ : ℂ → (Σ k, ι k) → ℂ := fun σ => s ((C.chart k).symm (L σ)) with hγdef`. Establish `hγd : ∀ σ ∈ T, DifferentiableAt ℂ γ σ` using `fun σ hσ => differentiableAt_pi.2 fun p => (hanal (L σ) hσ p).differentiableAt.comp σ (hLd σ).differentiableAt`. Establish `hγmem : ∀ σ ∈ T, γ σ ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (γ σ) = (C.chart k).symm (L σ)` using `fun σ hσ => hs _ hσ.2.1`. Establish `hγ0 : γ 0 = s ((C.chart k).symm y)` using `by simp [hγdef, hL0]`. Establish `hγw : HasDerivAt γ (deriv γ 0) 0` using `(hγd 0 hT0).hasDerivAt`.

Establish `hTn : T ∈ 𝓝 (0 : ℂ)` using `hTo.mem_nhds hT0`. Establish `hline : (fun σ => C.chart k (M.proj (γ σ))) =ᶠ[𝓝 0] L` using `by filter_upwards [hTn] with σ hσ`. Rewrite using `[(hγmem σ hσ).2, (C.chart k).right_inv hσ.1]`. Establish `hz : γ 0 ∈ mcPts (mCoordIdeal D.y)` using `(hγmem 0 hT0).1`. Establish `hpz : M.proj (γ 0) = (C.chart k).symm y` using `by rw [(hγmem 0 hT0).2, hL0]`.

Use `⟨γ 0, hz, hpz, deriv γ 0, ⟨γ, rfl, hγw, ?_, (hLd 0).congr_of_eventuallyEq hline⟩, ?_, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hTn] with σ hσ`. Conclude with `⟨hγd σ hσ, (hγmem σ hσ).1⟩`. Introduce `f hf`. Establish `hder` using `hasDerivAt_eval_comp (map (Int.castRingHom ℂ) f) hγw`.

Establish `hzero : (fun σ => eval (γ σ) (map (Int.castRingHom ℂ) f)) =ᶠ[𝓝 0] fun _ => (0 : ℂ)` using `by filter_upwards [hTn] with σ hσ`. Conclude with `(hγmem σ hσ).1.2 f hf`. Conclude with `hder.unique ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hzero)`. Introduce `c hwc`. Take `⟨W, hWo, hzW, F, hFd, hF⟩` from `hP II Ψ K ι Ω E D M (C.chart k) hcompat (γ 0) hz (by rw [hpz]; exact hx)`.

Establish `hFz : HasFDerivAt F (fderiv ℂ F (γ 0)) (γ 0)` using `(hFd.differentiableAt (hWo.mem_nhds hzW)).hasFDerivAt`. Establish `hWγ : ∀ᶠ σ in 𝓝 (0 : ℂ), γ σ ∈ W` using `hγw.continuousAt.preimage_mem_nhds (hWo.mem_nhds hzW)`. Establish `h1 : fderiv ℂ F (γ 0) (deriv γ 0) = v`. Use `(hFz.comp_hasDerivAt (0 : ℂ) hγw).unique ((hLd 0).congr_of_eventuallyEq ?_)` and prove the remaining obligations. Use `filter_upwards [hTn, hWγ, hline] with σ hσ hσW hσl`.

Rewrite using `[Function.comp_apply, ← (hF (γ σ) ⟨hσW, (hγmem σ hσ).1⟩).2]`. Conclude with `hσl`. Use `set δ : ℂ → (Σ k, ι k) → ℂ := fun σ => torusSmul (fun k => Complex.exp (σ * c k)) (γ 0) with hδ`. Establish `hδ0 : δ 0 = γ 0`. Use function extensionality and compare the values at `p`.

Simplify using `[hδ, torusSmul]`. Establish `hδd : HasDerivAt δ (torusSmul c (γ 0)) 0`. Use `hasDerivAt_pi.2 fun p => ?_` and prove the remaining obligations. Establish `h` using `(((hasDerivAt_id (0 : ℂ)).mul_const (c p.1)).cexp).mul_const (γ 0 p)`. Simplify `h` using `[hδ, torusSmul]`.

Establish `hδmem : ∀ σ, δ σ ∈ mcPts (mCoordIdeal D.y)` using `fun σ => ComponentDataEquivalence.mcPts_torus D.arith.2.1.2.1 hz fun k => Complex.exp_ne_zero _`. Establish `hδproj : ∀ σ, M.proj (δ σ) = M.proj (γ 0)` using `fun σ => ((M.fibre (γ 0) hz (δ σ) (hδmem σ)).2 ⟨_, fun k => Complex.exp_ne_zero _, rfl⟩).symm`. Establish `hWδ : ∀ᶠ σ in 𝓝 (0 : ℂ), δ σ ∈ W`. Use `hδd.continuousAt.preimage_mem_nhds (hWo.mem_nhds (hδ0 ▸ hzW))` as an intermediate fact. Conclude with `this`.

Establish `h2 : fderiv ℂ F (γ 0) (torusSmul c (γ 0)) = 0`. Establish `hFz' : HasFDerivAt F (fderiv ℂ F (γ 0)) (δ 0)` using `hδ0 ▸ hFz`. Use `(hFz'.comp_hasDerivAt (0 : ℂ) hδd).unique ((hasDerivAt_const (0 : ℂ) (C.chart k (M.proj (γ 0)))).congr_of_eventuallyEq ?_)` and prove the remaining obligations. Use `filter_upwards [hWδ] with σ hσW`. Rewrite using `[Function.comp_apply, ← (hF (δ σ) ⟨hσW, hδmem σ⟩).2, hδproj σ]`.

Conclude with `hv (h1.symm.trans (hwc ▸ h2))`.
-/
theorem ChartVelLiftCharts.proof (hP : ProjHoloLocal.Statement) : ChartVelLiftCharts.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D M C k y hy v hv
  classical
  have hcompat : ReciprocityTheory.AnForm.M.IsCompatChart M.atlas (C.chart k) := C.compat k
  have hx : (C.chart k).symm y ∈ (C.chart k).source := (C.chart k).map_target hy
  obtain ⟨U, hUo, hxU, s, hs, hshol⟩ := M.sections ((C.chart k).symm y)
  obtain ⟨j, hj⟩ := M.atlas.cover ((C.chart k).symm y)

  set V : Set (Fin D.n → ℂ) := (C.chart k).target ∩
    (C.chart k).symm ⁻¹' (U ∩ (M.atlas.chart j).source) with hV
  have hVo : IsOpen V := (C.chart k).continuousOn_symm.isOpen_inter_preimage (C.chart k).open_target
    (hUo.inter (M.atlas.chart j).open_source)

  have hanal : ∀ u ∈ V, ∀ p, AnalyticAt ℂ (fun u => s ((C.chart k).symm u) p) u := by
    intro u hu p
    have h1 : AnalyticAt ℂ (M.atlas.chart j ∘ (C.chart k).symm) u :=
      (hcompat j).2 u ⟨hu.1, hu.2.2⟩
    have h2 : AnalyticAt ℂ ((fun y' => s y' p) ∘ (M.atlas.chart j).symm)
        ((M.atlas.chart j ∘ (C.chart k).symm) u) := by
      refine hshol p j _ ⟨(M.atlas.chart j).map_source hu.2.2, ?_⟩
      show (M.atlas.chart j).symm ((M.atlas.chart j) ((C.chart k).symm u)) ∈ U
      rw [(M.atlas.chart j).left_inv hu.2.2]
      exact hu.2.1
    refine (h2.comp h1).congr ?_
    filter_upwards [hVo.mem_nhds hu] with u' hu'
    simp only [Function.comp_apply]
    rw [(M.atlas.chart j).left_inv hu'.2.2]

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
  set γ : ℂ → (Σ k, ι k) → ℂ := fun σ => s ((C.chart k).symm (L σ)) with hγdef
  have hγd : ∀ σ ∈ T, DifferentiableAt ℂ γ σ := fun σ hσ =>
    differentiableAt_pi.2 fun p => (hanal (L σ) hσ p).differentiableAt.comp σ (hLd σ).differentiableAt
  have hγmem : ∀ σ ∈ T, γ σ ∈ mcPts (mCoordIdeal D.y) ∧
      M.proj (γ σ) = (C.chart k).symm (L σ) := fun σ hσ => hs _ hσ.2.1
  have hγ0 : γ 0 = s ((C.chart k).symm y) := by simp [hγdef, hL0]
  have hγw : HasDerivAt γ (deriv γ 0) 0 := (hγd 0 hT0).hasDerivAt
  have hTn : T ∈ 𝓝 (0 : ℂ) := hTo.mem_nhds hT0

  have hline : (fun σ => C.chart k (M.proj (γ σ))) =ᶠ[𝓝 0] L := by
    filter_upwards [hTn] with σ hσ
    rw [(hγmem σ hσ).2, (C.chart k).right_inv hσ.1]
  have hz : γ 0 ∈ mcPts (mCoordIdeal D.y) := (hγmem 0 hT0).1
  have hpz : M.proj (γ 0) = (C.chart k).symm y := by rw [(hγmem 0 hT0).2, hL0]
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
      hP II Ψ K ι Ω E D M (C.chart k) hcompat (γ 0) hz (by rw [hpz]; exact hx)
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
    have hδproj : ∀ σ, M.proj (δ σ) = M.proj (γ 0) := fun σ =>
      ((M.fibre (γ 0) hz (δ σ) (hδmem σ)).2 ⟨_, fun k => Complex.exp_ne_zero _, rfl⟩).symm
    have hWδ : ∀ᶠ σ in 𝓝 (0 : ℂ), δ σ ∈ W := by
      have := hδd.continuousAt.preimage_mem_nhds (hWo.mem_nhds (hδ0 ▸ hzW))
      exact this
    have h2 : fderiv ℂ F (γ 0) (torusSmul c (γ 0)) = 0 := by
      have hFz' : HasFDerivAt F (fderiv ℂ F (γ 0)) (δ 0) := hδ0 ▸ hFz
      refine (hFz'.comp_hasDerivAt (0 : ℂ) hδd).unique
        ((hasDerivAt_const (0 : ℂ) (C.chart k (M.proj (γ 0)))).congr_of_eventuallyEq ?_)
      filter_upwards [hWδ] with σ hσW
      rw [Function.comp_apply, ← (hF (δ σ) ⟨hσW, hδmem σ⟩).2, hδproj σ]
    exact hv (h1.symm.trans (hwc ▸ h2))

end GroundTheory.Heights₂.Heights.NineStatements

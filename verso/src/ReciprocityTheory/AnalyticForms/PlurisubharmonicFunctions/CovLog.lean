import ReciprocityTheory.AnalyticForms.MaIntEmpty

namespace ReciprocityTheory.AnForm.A

open Complex Filter Topology

noncomputable section

variable {D : ℕ}

/- English proof (translation)
Establish `h1 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ ψ` using `h.eventuallyEq_nhds.mono fun y hy => hy.fderiv_eq`. Establish `h2 : fderiv ℝ (fderiv ℝ φ) z = fderiv ℝ (fderiv ℝ ψ) z` using `h1.fderiv_eq`. Use extensionality with `i j`. Simplify using `only [hessC, h2]`.
-/
theorem hessC_congr' {φ ψ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (h : φ =ᶠ[𝓝 z] ψ) :
    hessC φ z = hessC ψ z := by
  have h1 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ ψ :=
    h.eventuallyEq_nhds.mono fun y hy => hy.fderiv_eq
  have h2 : fderiv ℝ (fderiv ℝ φ) z = fderiv ℝ (fderiv ℝ ψ) z := h1.fderiv_eq
  ext i j
  simp only [hessC, h2]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [hessC, hB, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, Matrix.zero_apply]`. Simplify using `only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]`. Put the polynomial expressions in normal form. Simplify using the standard rewrite rules.
-/
theorem hessC_eq_zero_of_re_bilin (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (B : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ) →L[ℂ] ℂ)
    (hB : ∀ v u, fderiv ℝ (fderiv ℝ φ) z v u = (B v u).re) : hessC φ z = 0 := by
  ext i j
  simp only [hessC, hB, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, Matrix.zero_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring_nf
  simp

/- English proof (translation)
Establish `hφ' : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ φ w` using `(hφ.eventually (by simp)).mono fun w hw => hw.differentiableAt (by simp)`. Establish `hψ' : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ ψ w` using `(hψ.eventually (by simp)).mono fun w hw => hw.differentiableAt (by simp)`. Establish `hE : fderiv ℝ (fun w => φ w + ψ w) =ᶠ[𝓝 z] fun w => fderiv ℝ φ w + fderiv ℝ ψ w` using `(hφ'.and hψ').mono fun w hw => fderiv_add hw.1 hw.2`. Establish `hdφ : DifferentiableAt ℝ (fderiv ℝ φ) z` using `(hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`. Establish `hdψ : DifferentiableAt ℝ (fderiv ℝ ψ) z` using `(hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`.

Establish `h2 : fderiv ℝ (fderiv ℝ (fun w => φ w + ψ w)) z = fderiv ℝ (fderiv ℝ φ) z + fderiv ℝ (fderiv ℝ ψ) z`. Rewrite using `[hE.fderiv_eq]`. Conclude with `fderiv_add hdφ hdψ`. Use extensionality with `i j`. Simplify using `only [hessC, h2, ContinuousLinearMap.add_apply, Matrix.add_apply]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hessC_add' (φ ψ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z)
    (hψ : ContDiffAt ℝ 2 ψ z) :
    hessC (fun w => φ w + ψ w) z = hessC φ z + hessC ψ z := by
  have hφ' : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ φ w :=
    (hφ.eventually (by simp)).mono fun w hw => hw.differentiableAt (by simp)
  have hψ' : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ ψ w :=
    (hψ.eventually (by simp)).mono fun w hw => hw.differentiableAt (by simp)
  have hE : fderiv ℝ (fun w => φ w + ψ w) =ᶠ[𝓝 z] fun w => fderiv ℝ φ w + fderiv ℝ ψ w :=
    (hφ'.and hψ').mono fun w hw => fderiv_add hw.1 hw.2
  have hdφ : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdψ : DifferentiableAt ℝ (fderiv ℝ ψ) z :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ (fun w => φ w + ψ w)) z =
      fderiv ℝ (fderiv ℝ φ) z + fderiv ℝ (fderiv ℝ ψ) z := by
    rw [hE.fderiv_eq]
    exact fderiv_add hdφ hdψ
  ext i j
  simp only [hessC, h2, ContinuousLinearMap.add_apply, Matrix.add_apply]
  push_cast
  ring

/- English proof (translation)
Establish `h : HasFDerivAt (fun w => (g w).re) (Complex.reCLM.comp ((fderiv ℂ g z).restrictScalars ℝ)) z` using `Complex.reCLM.hasFDerivAt.comp z (hg.hasFDerivAt.restrictScalars ℝ)`. Rewrite using `[h.fderiv]`. Both sides reduce to the same expression.
-/
private lemma fderiv_re_apply_lemma (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hg : DifferentiableAt ℂ g z) (v : Fin D → ℂ) :
    fderiv ℝ (fun w => (g w).re) z v = (fderiv ℂ g z v).re := by
  have h : HasFDerivAt (fun w => (g w).re)
      (Complex.reCLM.comp ((fderiv ℂ g z).restrictScalars ℝ)) z :=
    Complex.reCLM.hasFDerivAt.comp z (hg.hasFDerivAt.restrictScalars ℝ)
  rw [h.fderiv]
  rfl

/- English proof (translation)
Establish `hΦ : ContDiffAt ℝ 2 (fun w => (G w).re) z` using `Complex.reCLM.contDiff.contDiffAt.comp z ((hG.contDiffAt).restrict_scalars ℝ)`. Establish `hdΦ : DifferentiableAt ℝ (fderiv ℝ (fun w => (G w).re)) z` using `(hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`. Establish `hA : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ G w` using `hG.eventually_analyticAt`. Establish `hE : (fun w => fderiv ℝ (fun w => (G w).re) w u) =ᶠ[𝓝 z] fun w => (fderiv ℂ G w u).re` using `hA.mono fun w hw => fderiv_re_apply_lemma G w hw.differentiableAt u`. Establish `hdG : DifferentiableAt ℂ (fun w => fderiv ℂ G w u) z` using `(hG.fderiv.differentiableAt).clm_apply (differentiableAt_const u)`.

Establish `h1 : fderiv ℝ (fderiv ℝ (fun w => (G w).re)) z v u = fderiv ℝ (fun w => fderiv ℝ (fun w => (G w).re) w u) z v`. Rewrite using `[fderiv_clm_apply hdΦ (differentiableAt_const u)]`. Simplify using the standard rewrite rules. Establish `h2 : fderiv ℂ (fun w => fderiv ℂ G w u) z v = fderiv ℂ (fderiv ℂ G) z v u`. Rewrite using `[fderiv_clm_apply (hG.fderiv.differentiableAt) (differentiableAt_const u)]`.

Simplify using the standard rewrite rules. Rewrite using `[h1, hE.fderiv_eq, fderiv_re_apply_lemma _ z hdG v, h2]`.
-/
theorem fderiv_fderiv_re_analytic (G : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) (hG : AnalyticAt ℂ G z)
    (v u : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ (fun w => (G w).re)) z v u = (fderiv ℂ (fderiv ℂ G) z v u).re := by
  have hΦ : ContDiffAt ℝ 2 (fun w => (G w).re) z :=
    Complex.reCLM.contDiff.contDiffAt.comp z ((hG.contDiffAt).restrict_scalars ℝ)
  have hdΦ : DifferentiableAt ℝ (fderiv ℝ (fun w => (G w).re)) z :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hA : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ G w := hG.eventually_analyticAt
  have hE : (fun w => fderiv ℝ (fun w => (G w).re) w u) =ᶠ[𝓝 z]
      fun w => (fderiv ℂ G w u).re :=
    hA.mono fun w hw => fderiv_re_apply_lemma G w hw.differentiableAt u
  have hdG : DifferentiableAt ℂ (fun w => fderiv ℂ G w u) z :=
    (hG.fderiv.differentiableAt).clm_apply (differentiableAt_const u)
  have h1 : fderiv ℝ (fderiv ℝ (fun w => (G w).re)) z v u =
      fderiv ℝ (fun w => fderiv ℝ (fun w => (G w).re) w u) z v := by
    rw [fderiv_clm_apply hdΦ (differentiableAt_const u)]
    simp
  have h2 : fderiv ℂ (fun w => fderiv ℂ G w u) z v = fderiv ℂ (fderiv ℂ G) z v u := by
    rw [fderiv_clm_apply (hG.fderiv.differentiableAt) (differentiableAt_const u)]
    simp
  rw [h1, hE.fderiv_eq, fderiv_re_apply_lemma _ z hdG v, h2]

/- English proof (translation)
The claim follows from `hessC_eq_zero_of_re_bilin _ z _ (fderiv_fderiv_re_analytic G z hG)`.
-/
theorem hessC_re_analytic' (G : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) (hG : AnalyticAt ℂ G z) :
    hessC (fun w => (G w).re) z = 0 := hessC_eq_zero_of_re_bilin _ z _ (fderiv_fderiv_re_analytic G z hG)

/- English proof (translation)
Establish `hΦ : ContDiffAt ℝ 2 (fun w => (G w).re) z` using `Complex.reCLM.contDiff.contDiffAt.comp z ((hG.contDiffAt).restrict_scalars ℝ)`. Rewrite using `[hessC_add' φ _ z hφ hΦ, hessC_re_analytic' G z hG, add_zero]`.
-/
theorem hessC_add_re_analytic' (φ : (Fin D → ℂ) → ℝ) (G : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ z) (hG : AnalyticAt ℂ G z) :
    hessC (fun w => φ w + (G w).re) z = hessC φ z := by
  have hΦ : ContDiffAt ℝ 2 (fun w => (G w).re) z :=
    Complex.reCLM.contDiff.contDiffAt.comp z ((hG.contDiffAt).restrict_scalars ℝ)
  rw [hessC_add' φ _ z hφ hΦ, hessC_re_analytic' G z hG, add_zero]

/- English proof (translation)
Use `⟨fun w => Complex.log (g w / g z) + Complex.log (g z), ?_, ?_⟩` and prove the remaining obligations. Use `AnalyticAt.add ?_ analyticAt_const` and prove the remaining obligations. Use `(hg.div analyticAt_const hz).clog ?_` and prove the remaining obligations. Use `show g z / g z ∈ Complex.slitPlane`. Rewrite using `[div_self hz]`.

Conclude with `Complex.one_mem_slitPlane`. Use `filter_upwards [hg.continuousAt.eventually_ne hz] with w hw`. Simplify using `only [Complex.add_re, Complex.log_re, norm_div]`. Rewrite using `[Real.log_div (norm_ne_zero_iff.2 hw) (norm_ne_zero_iff.2 hz)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_re_analytic_eq_log_norm (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hg : AnalyticAt ℂ g z) (hz : g z ≠ 0) :
    ∃ G : (Fin D → ℂ) → ℂ, AnalyticAt ℂ G z ∧
      (fun w => Real.log ‖g w‖) =ᶠ[𝓝 z] fun w => (G w).re := by
  refine ⟨fun w => Complex.log (g w / g z) + Complex.log (g z), ?_, ?_⟩
  · refine AnalyticAt.add ?_ analyticAt_const
    refine (hg.div analyticAt_const hz).clog ?_
    show g z / g z ∈ Complex.slitPlane
    rw [div_self hz]
    exact Complex.one_mem_slitPlane
  · filter_upwards [hg.continuousAt.eventually_ne hz] with w hw
    simp only [Complex.add_re, Complex.log_re, norm_div]
    rw [Real.log_div (norm_ne_zero_iff.2 hw) (norm_ne_zero_iff.2 hz)]
    ring

/- English proof (translation)
Take `⟨G, hG, hEq⟩` from `exists_re_analytic_eq_log_norm g z hg hz`. Rewrite using `[hessC_congr' hEq]`. Conclude with `hessC_re_analytic' G z hG`.
-/
theorem hessC_log_norm' (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) (hg : AnalyticAt ℂ g z)
    (hz : g z ≠ 0) : hessC (fun w => Real.log ‖g w‖) z = 0 := by
  obtain ⟨G, hG, hEq⟩ := exists_re_analytic_eq_log_norm g z hg hz
  rw [hessC_congr' hEq]
  exact hessC_re_analytic' G z hG

/- English proof (translation)
Take `⟨G, hG, hEq⟩` from `exists_re_analytic_eq_log_norm g z hg hz`. Establish `h2 : (fun w => φ w + Real.log ‖g w‖) =ᶠ[𝓝 z] fun w => φ w + (G w).re` using `hEq.mono fun w hw => by simp only [hw]`. Rewrite using `[hessC_congr' h2]`. Conclude with `hessC_add_re_analytic' φ G z hφ hG`.
-/
theorem hessC_add_log_norm' (φ : (Fin D → ℂ) → ℝ) (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ z) (hg : AnalyticAt ℂ g z) (hz : g z ≠ 0) :
    hessC (fun w => φ w + Real.log ‖g w‖) z = hessC φ z := by
  obtain ⟨G, hG, hEq⟩ := exists_re_analytic_eq_log_norm g z hg hz
  have h2 : (fun w => φ w + Real.log ‖g w‖) =ᶠ[𝓝 z] fun w => φ w + (G w).re :=
    hEq.mono fun w hw => by simp only [hw]
  rw [hessC_congr' h2]
  exact hessC_add_re_analytic' φ G z hφ hG

end

end ReciprocityTheory.AnForm.A

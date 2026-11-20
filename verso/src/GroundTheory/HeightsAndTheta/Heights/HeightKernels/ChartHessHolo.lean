import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ChartMassAffine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix Filter Topology

noncomputable section

namespace ChartEnergySwapHessian

open ChartMongeAmpereAffineInvariance

variable {D : ℕ} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedSpace ℝ E']
  [IsScalarTower ℝ ℂ E']

/- English proof (translation)
Use `filter_upwards [hF.eventually (by simp)] with y' hy' v`. Rewrite using `[(hy'.differentiableAt (by norm_num)).fderiv_restrictScalars ℝ]`. Simplify using the standard rewrite rules.
-/
theorem eventually_fderiv_I_smul {F : (Fin D → ℂ) → E'} {y : Fin D → ℂ} (hF : ContDiffAt ℂ 2 F y) :
    ∀ᶠ y' in 𝓝 y, ∀ v, fderiv ℝ F y' (Complex.I • v) = Complex.I • fderiv ℝ F y' v := by
  filter_upwards [hF.eventually (by simp)] with y' hy' v
  rw [(hy'.differentiableAt (by norm_num)).fderiv_restrictScalars ℝ]
  simp

/- English proof (translation)
Establish `hR : ContDiffAt ℝ 2 F y` using `hF.restrict_scalars ℝ`. Establish `hd : DifferentiableAt ℝ (fderiv ℝ F) y` using `(hR.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`. Establish `h1 : HasFDerivAt (fun y' => fderiv ℝ F y' (Complex.I • v)) ((fderiv ℝ (fderiv ℝ F) y).flip (Complex.I • v)) y`. Simplify using `using hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Complex.I • v) y)`. Establish `h2 : HasFDerivAt (fun y' => Complex.I • fderiv ℝ F y' v) (Complex.I • (fderiv ℝ (fderiv ℝ F) y).flip v) y`.

Use `(hd.hasFDerivAt.clm_apply (hasFDerivAt_const v y)).const_smul Complex.I` as an intermediate fact. Simplify `this` using `[Pi.smul_def]`. Establish `h3` using `h2.congr_of_eventuallyEq ((eventually_fderiv_I_smul hF).mono fun y' hy' => hy' v)`. Use `congrArg (fun L => L u) (h1.unique h3)` as an intermediate fact. Simplify using `using this`.
-/
theorem fderiv_fderiv_I_right {F : (Fin D → ℂ) → E'} {y : Fin D → ℂ} (hF : ContDiffAt ℂ 2 F y)
    (u v : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ F) y u (Complex.I • v) = Complex.I • fderiv ℝ (fderiv ℝ F) y u v := by
  have hR : ContDiffAt ℝ 2 F y := hF.restrict_scalars ℝ
  have hd : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (hR.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 : HasFDerivAt (fun y' => fderiv ℝ F y' (Complex.I • v))
      ((fderiv ℝ (fderiv ℝ F) y).flip (Complex.I • v)) y := by
    simpa using hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Complex.I • v) y)
  have h2 : HasFDerivAt (fun y' => Complex.I • fderiv ℝ F y' v)
      (Complex.I • (fderiv ℝ (fderiv ℝ F) y).flip v) y := by
    have := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const v y)).const_smul Complex.I
    simpa [Pi.smul_def] using this
  have h3 := h2.congr_of_eventuallyEq ((eventually_fderiv_I_smul hF).mono fun y' hy' => hy' v)
  have := congrArg (fun L => L u) (h1.unique h3)
  simpa using this

omit [NormedSpace ℂ E'] [IsScalarTower ℝ ℂ E'] in

/- English proof (translation)
The claim follows from `hF.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) u v`.
-/
theorem fderiv_fderiv_symm {F : (Fin D → ℂ) → E'} {y : Fin D → ℂ} (hF : ContDiffAt ℝ 2 F y)
    (u v : Fin D → ℂ) : fderiv ℝ (fderiv ℝ F) y u v = fderiv ℝ (fderiv ℝ F) y v u :=
  hF.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) u v

/- English proof (translation)
Rewrite using `[fderiv_fderiv_symm (hF.restrict_scalars ℝ), fderiv_fderiv_I_right hF, fderiv_fderiv_symm (hF.restrict_scalars ℝ)]`.
-/
theorem fderiv_fderiv_I_left {F : (Fin D → ℂ) → E'} {y : Fin D → ℂ} (hF : ContDiffAt ℂ 2 F y)
    (u v : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ F) y (Complex.I • u) v = Complex.I • fderiv ℝ (fderiv ℝ F) y u v := by
  rw [fderiv_fderiv_symm (hF.restrict_scalars ℝ), fderiv_fderiv_I_right hF,
    fderiv_fderiv_symm (hF.restrict_scalars ℝ)]

/- English proof (translation)
Establish `hgev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ g (F y')` using `hF.continuousAt.tendsto.eventually ((hg.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num))`. Establish `hFev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ F y'` using `(hF.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num)`. Establish `heq : fderiv ℝ (fun y' => g (F y')) =ᶠ[𝓝 y] fun y' => (fderiv ℝ g (F y')).comp (fderiv ℝ F y')` using `by filter_upwards [hgev, hFev] with y' h1 h2`. Conclude with `fderiv_comp y' h1 h2`. Establish `hgd : DifferentiableAt ℝ (fderiv ℝ g) (F y)` using `(hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`.

Establish `hFd : DifferentiableAt ℝ (fderiv ℝ F) y` using `(hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`. Establish `hc : HasFDerivAt (fun y' => fderiv ℝ g (F y')) ((fderiv ℝ (fderiv ℝ g) (F y)).comp (fderiv ℝ F y)) y` using `hgd.hasFDerivAt.comp y (hF.differentiableAt (by norm_num)).hasFDerivAt`. Establish `hall` using `(hc.clm_comp hFd.hasFDerivAt).congr_of_eventuallyEq heq`. Rewrite using `[hall.fderiv]`. Simplify using `[add_comm]`.
-/
theorem fderiv_fderiv_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : G → ℝ}
    {F : (Fin D → ℂ) → G} {y : Fin D → ℂ} (hg : ContDiffAt ℝ 2 g (F y)) (hF : ContDiffAt ℝ 2 F y)
    (u v : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ fun y' => g (F y')) y u v =
      fderiv ℝ (fderiv ℝ g) (F y) (fderiv ℝ F y u) (fderiv ℝ F y v) +
        fderiv ℝ g (F y) (fderiv ℝ (fderiv ℝ F) y u v) := by
  have hgev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ g (F y') :=
    hF.continuousAt.tendsto.eventually
      ((hg.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num))
  have hFev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ F y' :=
    (hF.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num)
  have heq : fderiv ℝ (fun y' => g (F y')) =ᶠ[𝓝 y]
      fun y' => (fderiv ℝ g (F y')).comp (fderiv ℝ F y') := by
    filter_upwards [hgev, hFev] with y' h1 h2
    exact fderiv_comp y' h1 h2
  have hgd : DifferentiableAt ℝ (fderiv ℝ g) (F y) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hFd : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : HasFDerivAt (fun y' => fderiv ℝ g (F y'))
      ((fderiv ℝ (fderiv ℝ g) (F y)).comp (fderiv ℝ F y)) y :=
    hgd.hasFDerivAt.comp y (hF.differentiableAt (by norm_num)).hasFDerivAt
  have hall := (hc.clm_comp hFd.hasFDerivAt).congr_of_eventuallyEq heq
  rw [hall.fderiv]
  simp [add_comm]

/- English proof (translation)
Establish `heq : fderiv ℝ (fun y' => f₁ y' + f₂ y') =ᶠ[𝓝 y] fun y' => fderiv ℝ f₁ y' + fderiv ℝ f₂ y'` using `by filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp)] with y' a b`. Conclude with `fderiv_add (a.differentiableAt (by norm_num)) (b.differentiableAt (by norm_num))`. Establish `hd₁ : DifferentiableAt ℝ (fderiv ℝ f₁) y` using `(h₁.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`. Establish `hd₂ : DifferentiableAt ℝ (fderiv ℝ f₂) y` using `(h₂.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`. Conclude with `((hd₁.hasFDerivAt.add hd₂.hasFDerivAt).congr_of_eventuallyEq heq).fderiv`.
-/
theorem fderiv_fderiv_add {f₁ f₂ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h₁ : ContDiffAt ℝ 2 f₁ y)
    (h₂ : ContDiffAt ℝ 2 f₂ y) :
    fderiv ℝ (fderiv ℝ fun y' => f₁ y' + f₂ y') y = fderiv ℝ (fderiv ℝ f₁) y + fderiv ℝ (fderiv ℝ f₂) y := by
  have heq : fderiv ℝ (fun y' => f₁ y' + f₂ y') =ᶠ[𝓝 y] fun y' => fderiv ℝ f₁ y' + fderiv ℝ f₂ y' := by
    filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp)] with y' a b
    exact fderiv_add (a.differentiableAt (by norm_num)) (b.differentiableAt (by norm_num))
  have hd₁ : DifferentiableAt ℝ (fderiv ℝ f₁) y :=
    (h₁.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd₂ : DifferentiableAt ℝ (fderiv ℝ f₂) y :=
    (h₂.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact ((hd₁.hasFDerivAt.add hd₂.hasFDerivAt).congr_of_eventuallyEq heq).fderiv

/- English proof (translation)
Simplify using `only [sesq, hH, map_smul]`. Rewrite using `[hR₁, hR₂]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sesq_eq_of_form (H H₀ : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)
    (L : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ)) (R : (Fin D → ℂ) → (Fin D → ℂ) → ℝ)
    (hH : ∀ u v, H u v = H₀ (L u) (L v) + R u v)
    (hR₁ : ∀ u v, R (Complex.I • u) (Complex.I • v) = -R u v)
    (hR₂ : ∀ u v, R u (Complex.I • v) = R (Complex.I • u) v) (a b : Fin D → ℂ) :
    sesq H a b = sesq H₀ (L a) (L b) := by
  simp only [sesq, hH, map_smul]
  rw [hR₁, hR₂]
  push_cast
  ring

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[cxHessian_eq_sesq, sesq_eq_of_form _ _ L R hH hR₁ hR₂, sesq_expand]`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul, LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Establish `hc : cxHessian g w l k = sesq (fderiv ℝ (fderiv ℝ g) w) (Pi.single l 1) (Pi.single k 1)` using `rfl`. Simplify using `only [hc, starRingEnd_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cxHessian_of_form (f g : (Fin D → ℂ) → ℝ) (y w : Fin D → ℂ) (L : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ))
    (R : (Fin D → ℂ) → (Fin D → ℂ) → ℝ)
    (hH : ∀ u v, fderiv ℝ (fderiv ℝ f) y u v = fderiv ℝ (fderiv ℝ g) w (L u) (L v) + R u v)
    (hR₁ : ∀ u v, R (Complex.I • u) (Complex.I • v) = -R u v)
    (hR₂ : ∀ u v, R u (Complex.I • v) = R (Complex.I • u) v) :
    cxHessian f y = (LinearMap.toMatrix' (L : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)))ᵀ * cxHessian g w *
      (LinearMap.toMatrix' (L : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).map (starRingEnd ℂ) := by
  ext i j
  rw [cxHessian_eq_sesq, sesq_eq_of_form _ _ L R hH hR₁ hR₂, sesq_expand]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
    LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hc : cxHessian g w l k = sesq (fderiv ℝ (fderiv ℝ g) w) (Pi.single l 1) (Pi.single k 1) := rfl
  simp only [hc, starRingEnd_apply]
  ring

/- English proof (translation)
Establish `hFR : ContDiffAt ℝ 2 F y` using `hF.restrict_scalars ℝ`. Establish `hhR : ContDiffAt ℝ 2 h y` using `hh.restrict_scalars ℝ`. Establish `hHess : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ fun y' => g (F y') + (h y').re) y`. Establish `: fderiv ℝ f =ᶠ[𝓝 y] fderiv ℝ (fun y' => g (F y') + (h y').re)` using `hf.eventuallyEq_nhds.mono fun _ h' => h'.fderiv_eq`. Conclude with `this.fderiv_eq`.

Establish `hre2 : ContDiffAt ℝ 2 (fun y' => (h y').re) y` using `Complex.reCLM.contDiff.contDiffAt.comp y hhR`. Establish `hsum` using `fderiv_fderiv_add (f₁ := fun y' => g (F y')) (f₂ := fun y' => (h y').re) (hg.comp y hFR) hre2`. Establish `hre : ∀ u v, fderiv ℝ (fderiv ℝ fun y' => (h y').re) y u v = Complex.reCLM (fderiv ℝ (fderiv ℝ h) y u v)`. Introduce `u v`. Use `fderiv_fderiv_comp (g := ⇑Complex.reCLM) (F := h) Complex.reCLM.contDiff.contDiffAt hhR u v` as an intermediate fact.

Establish `h0 : fderiv ℝ (fderiv ℝ (⇑Complex.reCLM)) (h y) = 0`. Establish `: fderiv ℝ (⇑Complex.reCLM) = fun _ => Complex.reCLM` using `funext fun _ => Complex.reCLM.fderiv`. Rewrite using `[this]`. Conclude with `fderiv_const_apply _`. Rewrite `this` using `[h0, Complex.reCLM.fderiv]`.

Simplify using `using this`. Establish `hLF : ∀ u, fderiv ℝ F y u = fderiv ℂ F y u` using `fun u => by`. Rewrite using `[(hF.differentiableAt (by norm_num)).fderiv_restrictScalars ℝ]`. Both sides reduce to the same expression. Use `cxHessian_of_form f g y (F y) (fderiv ℂ F y) (fun u v => fderiv ℝ g (F y) (fderiv ℝ (fderiv ℝ F) y u v) + Complex.reCLM (fderiv ℝ (fderiv ℝ h) y u v)) ?_ ?_ ?_` and prove the remaining obligations.

Introduce `u v`. Rewrite using `[hHess, hsum, _root_.add_apply, _root_.add_apply, fderiv_fderiv_comp hg hFR, hre, hLF, hLF]`. Expand and normalize the polynomial expressions, which then agree. Introduce `u v`. Simplify using `only [fderiv_fderiv_I_left hF, fderiv_fderiv_I_right hF, fderiv_fderiv_I_left hh, fderiv_fderiv_I_right hh, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `u v`. Simplify using `only [fderiv_fderiv_I_left hF, fderiv_fderiv_I_right hF, fderiv_fderiv_I_left hh, fderiv_fderiv_I_right hh]`.
-/
theorem cxHessian_comp_holo (f g : (Fin D → ℂ) → ℝ) (F : (Fin D → ℂ) → (Fin D → ℂ)) (h : (Fin D → ℂ) → ℂ)
    (y : Fin D → ℂ) (hg : ContDiffAt ℝ 2 g (F y)) (hF : ContDiffAt ℂ 2 F y) (hh : ContDiffAt ℂ 2 h y)
    (hf : f =ᶠ[𝓝 y] fun y' => g (F y') + (h y').re) :
    cxHessian f y = (LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)))ᵀ *
      cxHessian g (F y) * (LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).map
        (starRingEnd ℂ) := by
  have hFR : ContDiffAt ℝ 2 F y := hF.restrict_scalars ℝ
  have hhR : ContDiffAt ℝ 2 h y := hh.restrict_scalars ℝ
  have hHess : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ fun y' => g (F y') + (h y').re) y := by
    have : fderiv ℝ f =ᶠ[𝓝 y] fderiv ℝ (fun y' => g (F y') + (h y').re) :=
      hf.eventuallyEq_nhds.mono fun _ h' => h'.fderiv_eq
    exact this.fderiv_eq
  have hre2 : ContDiffAt ℝ 2 (fun y' => (h y').re) y := Complex.reCLM.contDiff.contDiffAt.comp y hhR
  have hsum := fderiv_fderiv_add (f₁ := fun y' => g (F y')) (f₂ := fun y' => (h y').re) (hg.comp y hFR) hre2
  have hre : ∀ u v, fderiv ℝ (fderiv ℝ fun y' => (h y').re) y u v =
      Complex.reCLM (fderiv ℝ (fderiv ℝ h) y u v) := by
    intro u v
    have := fderiv_fderiv_comp (g := ⇑Complex.reCLM) (F := h) Complex.reCLM.contDiff.contDiffAt hhR u v
    have h0 : fderiv ℝ (fderiv ℝ (⇑Complex.reCLM)) (h y) = 0 := by
      have : fderiv ℝ (⇑Complex.reCLM) = fun _ => Complex.reCLM := funext fun _ => Complex.reCLM.fderiv
      rw [this]
      exact fderiv_const_apply _
    rw [h0, Complex.reCLM.fderiv] at this
    simpa using this
  have hLF : ∀ u, fderiv ℝ F y u = fderiv ℂ F y u := fun u => by
    rw [(hF.differentiableAt (by norm_num)).fderiv_restrictScalars ℝ]
    rfl
  refine cxHessian_of_form f g y (F y) (fderiv ℂ F y)
    (fun u v => fderiv ℝ g (F y) (fderiv ℝ (fderiv ℝ F) y u v) + Complex.reCLM (fderiv ℝ (fderiv ℝ h) y u v))
    ?_ ?_ ?_
  · intro u v
    rw [hHess, hsum, _root_.add_apply, _root_.add_apply, fderiv_fderiv_comp hg hFR,
      hre, hLF, hLF]
    ring
  · intro u v
    simp only [fderiv_fderiv_I_left hF, fderiv_fderiv_I_right hF, fderiv_fderiv_I_left hh,
      fderiv_fderiv_I_right hh, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]
    ring
  · intro u v
    simp only [fderiv_fderiv_I_left hF, fderiv_fderiv_I_right hF, fderiv_fderiv_I_left hh,
      fderiv_fderiv_I_right hh]

/- English proof (translation)
Use `set J := LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) with hJ`. Establish `hQ : (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det` using `(RingHom.map_det (starRingEnd ℂ) J).symm`. Establish `hH : ∀ j, cxHessian (Φ' j) y = Jᵀ * cxHessian (Φ j) (F y) * J.map (starRingEnd ℂ)` using `fun j => cxHessian_comp_holo (Φ' j) (Φ j) F h y (hΦ j) hF hh (hΦ' j)`. Simplify using `only [maDensity, hH]`. Rewrite using `[mixedDisc_mul_mul (Jᵀ) (J.map (starRingEnd ℂ)) (fun j => cxHessian (Φ j) (F y)), det_transpose, hQ, Complex.mul_conj, Complex.re_ofReal_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem maDensity_comp_holo (Φ' Φ : Fin D → (Fin D → ℂ) → ℝ) (F : (Fin D → ℂ) → (Fin D → ℂ))
    (h : (Fin D → ℂ) → ℂ) (y : Fin D → ℂ) (hΦ : ∀ j, ContDiffAt ℝ 2 (Φ j) (F y)) (hF : ContDiffAt ℂ 2 F y)
    (hh : ContDiffAt ℂ 2 h y) (hΦ' : ∀ j, Φ' j =ᶠ[𝓝 y] fun y' => Φ j (F y') + (h y').re) :
    maDensity Φ' y = Complex.normSq (LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).det *
      maDensity Φ (F y) := by
  set J := LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) with hJ
  have hQ : (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det := (RingHom.map_det (starRingEnd ℂ) J).symm
  have hH : ∀ j, cxHessian (Φ' j) y = Jᵀ * cxHessian (Φ j) (F y) * J.map (starRingEnd ℂ) := fun j =>
    cxHessian_comp_holo (Φ' j) (Φ j) F h y (hΦ j) hF hh (hΦ' j)
  simp only [maDensity, hH]
  rw [mixedDisc_mul_mul (Jᵀ) (J.map (starRingEnd ℂ)) (fun j => cxHessian (Φ j) (F y)), det_transpose, hQ,
    Complex.mul_conj, Complex.re_ofReal_mul]
  ring

/- English proof (translation)
Rewrite using `[hF.fderiv_restrictScalars ℝ, LinearMap.det_toMatrix']`. Establish `: ((ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ F y) : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)) = ((fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).restrictScalars ℝ` using `rfl`. Rewrite using `[ContinuousLinearMap.det, this, LinearMap.det_restrictScalars, Algebra.norm_complex_apply]`.
-/
theorem det_fderiv_real {F : (Fin D → ℂ) → (Fin D → ℂ)} {y : Fin D → ℂ} (hF : DifferentiableAt ℂ F y) :
    (fderiv ℝ F y).det =
      Complex.normSq (LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).det := by
  rw [hF.fderiv_restrictScalars ℝ, LinearMap.det_toMatrix']
  have : ((ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ F y) : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) :
      (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)) =
      ((fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).restrictScalars ℝ := rfl
  rw [ContinuousLinearMap.det, this, LinearMap.det_restrictScalars, Algebra.norm_complex_apply]

end ChartEnergySwapHessian

end

end GroundTheory.Heights₂.Heights

import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConeTangentLiftInChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Cusp
open GroundTheory.Heights₂.Heights.LowerBoundFree (torusSmul)
open ReciprocityTheory.AnForm

namespace RootFieldNumerics.Levi

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

/- English proof (translation)
Establish `hz` using `hpts.self_of_nhds`. Establish `hdim` using `finrank_tanSub_pC_le Ω y _ hP hsm hz`. Establish `hzI : ∀ f ∈ pC (mCoordIdeal y), eval (γ t) f = 0`. Establish `h` using `hz`. Rewrite `h` using `[mcPts_eq_pC]`.

Conclude with `h.2`. Establish `hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y))` using `isMultiHomogIdeal_pC hP.2.1.2.1`. Establish `hcone : ∀ x, IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal y) (γ t) x → x ∈ tanSub (pC (mCoordIdeal y)) (γ t)`. Introduce `x hx f hf`. Establish `hle : pC (mCoordIdeal y) ≤ tanIdeal (γ t) x`.

Rewrite using `[pC, Ideal.span_le]`. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Conclude with `⟨hz.2 g hg, hx g hg⟩`. Conclude with `(hle hf).2`. Set `L₁ : (Fin e → ℂ) →ₗ[ℂ] (Σ k, J k) → ℂ` to `(fderiv ℂ γ t).toLinearMap`.

Set `L₂ : (K → ℂ) →ₗ[ℂ] (Σ k, J k) → ℂ` to `{ toFun := fun c => torusSmul c (γ t) map_add' := fun c c' => by funext q; simp only [torusSmul, Pi.add_apply]; ring map_smul' := fun r c => by`. Use function extensionality and compare the values at `q`. Simplify using `only [torusSmul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]`. Use `ring }`. Set `L` to `L₁.coprod L₂`.

Establish `hL : ∀ u c, L (u, c) = fderiv ℂ γ t u + torusSmul c (γ t)` using `fun _ _ => rfl`. Establish `hrange : LinearMap.range L ≤ tanSub (pC (mCoordIdeal y)) (γ t)`. Introduce and unpack `_ ⟨⟨u, c⟩, rfl⟩`. Rewrite using `[hL]`. Use `Submodule.add_mem _ (hcone _ ?_) fun f hf => (le_tanIdeal_torusSmul hPh hzI c hf).2` and prove the remaining obligations.

Conclude with `GroundTheory.Heights₂.Heights.HilbertSamuel.G1.isConeTangent_of_sheet le_rfl hγ hpts u`. Establish `hinj : Function.Injective L`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce and unpack `⟨u, c⟩ h`. Rewrite `h` using `[hL]`.

Establish `hu : u = 0` using `himm u (fun k => -c k) (by`. Use function extensionality and compare the values at `q`. Establish `h1` using `congrFun h q`. Simplify using `only [torusSmul, Pi.add_apply, Pi.zero_apply] at h1 ⊢`. Take the linear combination `h1)`.

Substitute `hu` using the available equality. Establish `h2 : torusSmul c (γ t) = 0` using `by simpa using h`. Establish `hc : c = 0`. Use function extensionality and compare the values at `k`. Take `⟨i, hi⟩` from `hz.1 k`.

Establish `h3 : c k * γ t ⟨k, i⟩ = 0` using `congrFun h2 ⟨k, i⟩`. Conclude with `(mul_eq_zero.mp h3).resolve_right hi`. Rewrite using `[hc]`. Both sides reduce to the same expression. Establish `hfr : Module.finrank ℂ (LinearMap.range L) = e + Fintype.card K`.

Rewrite using `[LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]`. Establish `heq` using `Submodule.eq_of_le_of_finrank_le hrange (by rw [hfr]; exact hdim)`. Establish `hvr : v ∈ LinearMap.range L` using `heq ▸ hcone v hv`. Take `⟨⟨u, c⟩, huc⟩` from `hvr`. Conclude with `⟨u, c, huc.symm⟩`.
-/
theorem tangent_decomp (Ω : Type) [Field Ω] [Algebra ℚ Ω] (y : (Σ k, J k) → Ω) (e : ℕ)
    (hP : IsArithVar (mCoordIdeal y) (e + 1)) (hsm : SmoothGenericFibreM y)
    (γ : (Fin e → ℂ) → (Σ k, J k) → ℂ) (t : Fin e → ℂ) (hγ : AnalyticAt ℂ γ t)
    (hpts : ∀ᶠ t' in 𝓝 t, γ t' ∈ mcPts (mCoordIdeal y))
    (himm : ∀ u c, fderiv ℂ γ t u = torusSmul c (γ t) → u = 0) (v : (Σ k, J k) → ℂ)
    (hv : IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal y) (γ t) v) :
    ∃ (u : Fin e → ℂ) (c : K → ℂ), v = fderiv ℂ γ t u + torusSmul c (γ t) := by
  classical
  have hz := hpts.self_of_nhds
  have hdim := finrank_tanSub_pC_le Ω y _ hP hsm hz
  have hzI : ∀ f ∈ pC (mCoordIdeal y), eval (γ t) f = 0 := by
    have h := hz
    rw [mcPts_eq_pC] at h
    exact h.2
  have hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) :=
    isMultiHomogIdeal_pC hP.2.1.2.1
  have hcone : ∀ x, IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal y) (γ t) x →
      x ∈ tanSub (pC (mCoordIdeal y)) (γ t) := by
    intro x hx f hf
    have hle : pC (mCoordIdeal y) ≤ tanIdeal (γ t) x := by
      rw [pC, Ideal.span_le]
      rintro _ ⟨g, hg, rfl⟩
      exact ⟨hz.2 g hg, hx g hg⟩
    exact (hle hf).2
  let L₁ : (Fin e → ℂ) →ₗ[ℂ] (Σ k, J k) → ℂ := (fderiv ℂ γ t).toLinearMap
  let L₂ : (K → ℂ) →ₗ[ℂ] (Σ k, J k) → ℂ :=
    { toFun := fun c => torusSmul c (γ t)
      map_add' := fun c c' => by funext q; simp only [torusSmul, Pi.add_apply]; ring
      map_smul' := fun r c => by
        funext q; simp only [torusSmul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  let L := L₁.coprod L₂
  have hL : ∀ u c, L (u, c) = fderiv ℂ γ t u + torusSmul c (γ t) := fun _ _ => rfl
  have hrange : LinearMap.range L ≤ tanSub (pC (mCoordIdeal y)) (γ t) := by
    rintro _ ⟨⟨u, c⟩, rfl⟩
    rw [hL]
    refine Submodule.add_mem _ (hcone _ ?_) fun f hf => (le_tanIdeal_torusSmul hPh hzI c hf).2
    exact GroundTheory.Heights₂.Heights.HilbertSamuel.G1.isConeTangent_of_sheet le_rfl hγ hpts u
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨u, c⟩ h
    rw [hL] at h
    have hu : u = 0 := himm u (fun k => -c k) (by
      funext q
      have h1 := congrFun h q
      simp only [torusSmul, Pi.add_apply, Pi.zero_apply] at h1 ⊢
      linear_combination h1)
    subst hu
    have h2 : torusSmul c (γ t) = 0 := by simpa using h
    have hc : c = 0 := by
      funext k
      obtain ⟨i, hi⟩ := hz.1 k
      have h3 : c k * γ t ⟨k, i⟩ = 0 := congrFun h2 ⟨k, i⟩
      exact (mul_eq_zero.mp h3).resolve_right hi
    rw [hc]
    rfl
  have hfr : Module.finrank ℂ (LinearMap.range L) = e + Fintype.card K := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have heq := Submodule.eq_of_le_of_finrank_le hrange (by rw [hfr]; exact hdim)
  have hvr : v ∈ LinearMap.range L := heq ▸ hcone v hv
  obtain ⟨⟨u, c⟩, huc⟩ := hvr
  exact ⟨u, c, huc.symm⟩

/- English proof (translation)
Use `differentiableAt_pi.2 fun q => ?_` and prove the remaining obligations. Establish `h1 : AnalyticAt ℂ (fun v : (Σ k, J k) → ℂ => v q) z` using `(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) q).analyticAt z`. Establish `h2 : AnalyticAt ℂ (fun v : (Σ k, J k) → ℂ => v ⟨q.1, p q.1⟩) z` using `(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) ⟨q.1, p q.1⟩).analyticAt z`. Conclude with `(h1.div h2 (hp q.1)).differentiableAt`.
-/
theorem differentiableAt_affCoord (p : (k : K) → J k) (z : (Σ k, J k) → ℂ) (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    DifferentiableAt ℂ (affCoord p) z := by
  refine differentiableAt_pi.2 fun q => ?_
  have h1 : AnalyticAt ℂ (fun v : (Σ k, J k) → ℂ => v q) z :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) q).analyticAt z
  have h2 : AnalyticAt ℂ (fun v : (Σ k, J k) → ℂ => v ⟨q.1, p q.1⟩) z :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) ⟨q.1, p q.1⟩).analyticAt z
  exact (h1.div h2 (hp q.1)).differentiableAt

/- English proof (translation)
Use function extensionality and compare the values at `q`. Simplify using `only [affCoord, torusSmul]`. Conclude with `mul_div_mul_left _ _ (hc q.1)`.
-/
theorem affCoord_torus (p : (k : K) → J k) (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, J k) → ℂ) :
    affCoord p (torusSmul c z) = affCoord p z := by
  funext q
  simp only [affCoord, torusSmul]
  exact mul_div_mul_left _ _ (hc q.1)

/- English proof (translation)
Establish `h1 : HasDerivAt (fun s : ℂ => torusSmul (fun k => Complex.exp (s * b k)) z) (torusSmul b z) 0`. Use `hasDerivAt_pi.2 fun q => ?_` and prove the remaining obligations. Use `(((hasDerivAt_id (0 : ℂ)).mul_const (b q.1)).cexp).mul_const (z q)` as an intermediate fact. Simplify `this` using `[torusSmul]`. Establish `h0 : torusSmul (fun k => Complex.exp ((0 : ℂ) * b k)) z = z`.

Use function extensionality and compare the values at `q`. Simplify using `[torusSmul]`. Establish `h2 : HasFDerivAt (affCoord p) (fderiv ℂ (affCoord p) z) (torusSmul (fun k => Complex.exp ((0 : ℂ) * b k)) z)`. Rewrite using `[h0]`. Conclude with `(differentiableAt_affCoord p z hp).hasFDerivAt`.

Establish `h3` using `h2.comp_hasDerivAt (0 : ℂ) h1`. Establish `h4 : (affCoord p ∘ fun s : ℂ => torusSmul (fun k => Complex.exp (s * b k)) z) = fun _ => affCoord p z`. Use function extensionality and compare the values at `s`. Conclude with `affCoord_torus p _ (fun k => Complex.exp_ne_zero _) z`. Rewrite `h3` using `[h4]`.

Conclude with `h3.unique (hasDerivAt_const _ _)`.
-/
theorem fderiv_affCoord_torus (p : (k : K) → J k) (z : (Σ k, J k) → ℂ) (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) (b : K → ℂ) :
    fderiv ℂ (affCoord p) z (torusSmul b z) = 0 := by
  have h1 : HasDerivAt (fun s : ℂ => torusSmul (fun k => Complex.exp (s * b k)) z) (torusSmul b z) 0 := by
    refine hasDerivAt_pi.2 fun q => ?_
    have := (((hasDerivAt_id (0 : ℂ)).mul_const (b q.1)).cexp).mul_const (z q)
    simpa [torusSmul] using this
  have h0 : torusSmul (fun k => Complex.exp ((0 : ℂ) * b k)) z = z := by
    funext q; simp [torusSmul]
  have h2 : HasFDerivAt (affCoord p) (fderiv ℂ (affCoord p) z)
      (torusSmul (fun k => Complex.exp ((0 : ℂ) * b k)) z) := by
    rw [h0]; exact (differentiableAt_affCoord p z hp).hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℂ) h1
  have h4 : (affCoord p ∘ fun s : ℂ => torusSmul (fun k => Complex.exp (s * b k)) z) = fun _ => affCoord p z := by
    funext s
    exact affCoord_torus p _ (fun k => Complex.exp_ne_zero _) z
  rw [h4] at h3
  exact h3.unique (hasDerivAt_const _ _)

/- English proof (translation)
Set `ℓ : (Unit → ℂ) →L[ℂ] ℂ` to `ContinuousLinearMap.proj ()`. Set `lin : (Unit → ℂ) → Fin e → ℂ` to `fun s => t + ℓ s • u`. Establish `hlin : HasFDerivAt lin (ℓ.smulRight u) 0`. Use `(ℓ.smulRight u).hasFDerivAt (x := 0)` as an intermediate fact. Conclude with `this.const_add t`.

Establish `hlinA : AnalyticAt ℂ lin 0` using `analyticAt_const.add ((ℓ.smulRight u).analyticAt 0)`. Establish `hl0 : lin 0 = t` using `by simp [lin]`. Establish `hγ' : AnalyticAt ℂ γ (lin 0)` using `by rw [hl0]; exact hγ`. Set `Γ : (Unit → ℂ) → (Σ k, J k) → ℂ` to `fun s => torusSmul (fun k => Complex.exp (ℓ s * b k)) (γ (lin s))`. Establish `hΓ0 : Γ 0 = γ t`.

Use function extensionality and compare the values at `q`. Simplify using `[Γ, torusSmul, hl0]`. Establish `hγl : AnalyticAt ℂ (γ ∘ lin) 0` using `hγ'.comp hlinA`. Establish `hΓA : AnalyticAt ℂ Γ 0`. Use `analyticAt_pi_iff.2 fun q => ?_` and prove the remaining obligations.

Conclude with `(((ℓ.analyticAt 0).mul analyticAt_const).cexp').mul (analyticAt_pi_iff.1 hγl q)`. Establish `hΓd : fderiv ℂ Γ 0 (fun _ => 1) = fderiv ℂ γ t u + torusSmul b (γ t)`. Establish `hg : HasFDerivAt (γ ∘ lin) ((fderiv ℂ γ t).comp (ℓ.smulRight u)) 0`. Establish `h1 : HasFDerivAt γ (fderiv ℂ γ t) (lin 0)` using `by rw [hl0]; exact hγ.differentiableAt.hasFDerivAt`. Conclude with `h1.comp 0 hlin`.

Use function extensionality and compare the values at `q`. Establish `h1` using `(hasFDerivAt_pi'.1 hΓA.differentiableAt.hasFDerivAt q)`. Establish `h2` using `(((ℓ.hasFDerivAt (x := 0)).mul_const (b q.1)).cexp).mul (hasFDerivAt_pi'.1 hg q)`. Establish `h3` using `congrArg (fun L => L (fun _ => 1)) (h1.unique h2)`. Simplify using `only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.proj_apply] at h3`.

Rewrite using `[h3]`. Simplify using `[ℓ, hl0, torusSmul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hφγ : ContDiffAt ℝ 2 (φ ∘ γ) t` using `hφ.comp t (hγ.restrictScalars (𝕜 := ℝ)).contDiffAt`. Establish `e1` using `levi_comp (φ := φ) (τ := Γ) (z := 0) (fun _ => 1) hΓA (by rw [hΓ0]; exact hφ)`.

Rewrite `e1` using `[hΓ0, hΓd]`. Establish `e2` using `levi_comp (φ := φ ∘ γ) (τ := lin) (z := 0) (fun _ => 1) hlinA (by rw [hl0]; exact hφγ)`. Rewrite `e2` using `[hl0, hlin.fderiv]`. Establish `e3 : (ℓ.smulRight u) (fun _ => 1) = u` using `by simp [ℓ]`. Rewrite `e2` using `[e3]`.

Rewrite using `[← e1, ← e2]`. Set `G : (Unit → ℂ) → ℂ` to `fun s => ∑ k, (d k : ℂ) * (ℓ s * b k)`. Establish `hG : AnalyticAt ℂ G 0` using `Finset.analyticAt_fun_sum _ fun k _ => analyticAt_const.mul ((ℓ.analyticAt 0).mul analyticAt_const)`. Establish `hev : φ ∘ Γ =ᶠ[𝓝 0] fun s => ((φ ∘ γ) ∘ lin) s + 1 * (G s).re`. Establish `ht : Tendsto lin (𝓝 0) (𝓝 t)` using `by rw [← hl0]; exact hlinA.continuousAt`.

Use `filter_upwards [ht.eventually hpts] with s hs`. Simplify using `only [Function.comp_apply, Γ]`. Rewrite using `[hhom _ _ (fun k => Complex.exp_ne_zero _) hs, add_comm, one_mul]`. Use `congr 1`. Simplify using `only [G, Complex.re_sum, Complex.re_ofReal_mul, Complex.norm_exp, Real.log_exp]`.

Establish `hc1 : ContDiffAt ℝ 2 ((φ ∘ γ) ∘ lin) 0` using `ContDiffAt.comp 0 (by rw [hl0]; exact hφγ) (hlinA.restrictScalars (𝕜 := ℝ)).contDiffAt`. Establish `hc2 : ContDiffAt ℝ 2 (fun s => (G s).re) 0` using `Complex.reCLM.contDiff.contDiffAt.comp 0 (hG.restrictScalars (𝕜 := ℝ)).contDiffAt`. Rewrite using `[levi_congr hev, levi_add_smul 1 hc1 hc2, levi_re_analytic hG]`. Simplify using the standard rewrite rules.
-/
theorem levi_torus {e : ℕ} (φ : ((Σ k, J k) → ℂ) → ℝ) (d : K → ℝ)
    (hhom : ∀ (c : K → ℂ) (z : (Σ k, J k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      φ (torusSmul c z) = ∑ k, d k * Real.log ‖c k‖ + φ z)
    (γ : (Fin e → ℂ) → (Σ k, J k) → ℂ) (t : Fin e → ℂ) (hγ : AnalyticAt ℂ γ t)
    (hpts : ∀ᶠ t' in 𝓝 t, ∀ k, ∃ i, γ t' ⟨k, i⟩ ≠ 0) (hφ : ContDiffAt ℝ 2 φ (γ t)) (u : Fin e → ℂ) (b : K → ℂ) :
    levi φ (γ t) (fderiv ℂ γ t u + torusSmul b (γ t)) = levi (φ ∘ γ) t u := by
  let ℓ : (Unit → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj ()
  let lin : (Unit → ℂ) → Fin e → ℂ := fun s => t + ℓ s • u
  have hlin : HasFDerivAt lin (ℓ.smulRight u) 0 := by
    have := (ℓ.smulRight u).hasFDerivAt (x := 0)
    exact this.const_add t
  have hlinA : AnalyticAt ℂ lin 0 := analyticAt_const.add ((ℓ.smulRight u).analyticAt 0)
  have hl0 : lin 0 = t := by simp [lin]
  have hγ' : AnalyticAt ℂ γ (lin 0) := by rw [hl0]; exact hγ
  let Γ : (Unit → ℂ) → (Σ k, J k) → ℂ := fun s => torusSmul (fun k => Complex.exp (ℓ s * b k)) (γ (lin s))
  have hΓ0 : Γ 0 = γ t := by
    funext q; simp [Γ, torusSmul, hl0]
  have hγl : AnalyticAt ℂ (γ ∘ lin) 0 := hγ'.comp hlinA
  have hΓA : AnalyticAt ℂ Γ 0 := by
    refine analyticAt_pi_iff.2 fun q => ?_
    exact (((ℓ.analyticAt 0).mul analyticAt_const).cexp').mul (analyticAt_pi_iff.1 hγl q)
  have hΓd : fderiv ℂ Γ 0 (fun _ => 1) = fderiv ℂ γ t u + torusSmul b (γ t) := by
    have hg : HasFDerivAt (γ ∘ lin) ((fderiv ℂ γ t).comp (ℓ.smulRight u)) 0 := by
      have h1 : HasFDerivAt γ (fderiv ℂ γ t) (lin 0) := by rw [hl0]; exact hγ.differentiableAt.hasFDerivAt
      exact h1.comp 0 hlin
    funext q
    have h1 := (hasFDerivAt_pi'.1 hΓA.differentiableAt.hasFDerivAt q)
    have h2 := (((ℓ.hasFDerivAt (x := 0)).mul_const (b q.1)).cexp).mul (hasFDerivAt_pi'.1 hg q)
    have h3 := congrArg (fun L => L (fun _ => 1)) (h1.unique h2)
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.proj_apply] at h3
    rw [h3]
    simp [ℓ, hl0, torusSmul]
    ring
  have hφγ : ContDiffAt ℝ 2 (φ ∘ γ) t := hφ.comp t (hγ.restrictScalars (𝕜 := ℝ)).contDiffAt
  have e1 := levi_comp (φ := φ) (τ := Γ) (z := 0) (fun _ => 1) hΓA (by rw [hΓ0]; exact hφ)
  rw [hΓ0, hΓd] at e1
  have e2 := levi_comp (φ := φ ∘ γ) (τ := lin) (z := 0) (fun _ => 1) hlinA (by rw [hl0]; exact hφγ)
  rw [hl0, hlin.fderiv] at e2
  have e3 : (ℓ.smulRight u) (fun _ => 1) = u := by simp [ℓ]
  rw [e3] at e2
  rw [← e1, ← e2]
  let G : (Unit → ℂ) → ℂ := fun s => ∑ k, (d k : ℂ) * (ℓ s * b k)
  have hG : AnalyticAt ℂ G 0 :=
    Finset.analyticAt_fun_sum _ fun k _ => analyticAt_const.mul ((ℓ.analyticAt 0).mul analyticAt_const)
  have hev : φ ∘ Γ =ᶠ[𝓝 0] fun s => ((φ ∘ γ) ∘ lin) s + 1 * (G s).re := by
    have ht : Tendsto lin (𝓝 0) (𝓝 t) := by rw [← hl0]; exact hlinA.continuousAt
    filter_upwards [ht.eventually hpts] with s hs
    simp only [Function.comp_apply, Γ]
    rw [hhom _ _ (fun k => Complex.exp_ne_zero _) hs, add_comm, one_mul]
    congr 1
    simp only [G, Complex.re_sum, Complex.re_ofReal_mul, Complex.norm_exp, Real.log_exp]
  have hc1 : ContDiffAt ℝ 2 ((φ ∘ γ) ∘ lin) 0 :=
    ContDiffAt.comp 0 (by rw [hl0]; exact hφγ) (hlinA.restrictScalars (𝕜 := ℝ)).contDiffAt
  have hc2 : ContDiffAt ℝ 2 (fun s => (G s).re) 0 :=
    Complex.reCLM.contDiff.contDiffAt.comp 0 (hG.restrictScalars (𝕜 := ℝ)).contDiffAt
  rw [levi_congr hev, levi_add_smul 1 hc1 hc2, levi_re_analytic hG]
  simp

/- English proof (translation)
Establish `hno : ∀ z : (Σ k, J k) → ℂ, z ∉ mcPts B` using `fun z hz => by`. Substitute `hB` using the available equality. Simplify using `using hz.2 1 Submodule.mem_top`. Take `⟨x, c, hc, hx⟩` from `R.surj z hz (hno z)`. Take `⟨j, hj⟩` from `R.A.cover x`.

Set `γ₀ : (Fin e → ℂ) → (Σ k, J k) → ℂ` to `fun t => R.lift x ((R.A.chart j).symm t)`. Set `γ : (Fin e → ℂ) → (Σ k, J k) → ℂ` to `fun t => torusSmul (fun k => (c k)⁻¹) (γ₀ t)`. Establish `hci : ∀ k, (c k)⁻¹ ≠ 0` using `fun k => inv_ne_zero (hc k)`. Establish `hsx : (R.A.chart j).symm (R.A.chart j x) = x` using `(R.A.chart j).left_inv hj`. Establish `hmemO : R.A.chart j x ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x` using `⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, hsx]; exact R.mem_U x⟩`.

Establish `hO` using `((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds hmemO`. Establish `hγ₀A : AnalyticAt ℂ γ₀ (R.A.chart j x)` using `analyticAt_pi_iff.2 fun q => R.holo x q j _ hmemO`. Establish `hγA : AnalyticAt ℂ γ (R.A.chart j x)` using `analyticAt_pi_iff.2 fun q => analyticAt_const.mul (analyticAt_pi_iff.1 hγ₀A q)`. Establish `hγz : γ (R.A.chart j x) = z`. Use function extensionality and compare the values at `q`.

Simplify using `only [γ, γ₀, torusSmul, hsx, hx]`. Rewrite using `[← mul_assoc, inv_mul_cancel₀ (hc _), one_mul]`. Establish `h0pts : ∀ᶠ t in 𝓝 (R.A.chart j x), γ₀ t ∈ mcPts (mCoordIdeal y)` using `by filter_upwards [hO] with t ht using R.mem x _ ht.2`. Establish `hpts : ∀ᶠ t in 𝓝 (R.A.chart j x), γ t ∈ mcPts (mCoordIdeal y)` using `by filter_upwards [h0pts] with t ht`. Conclude with `mcPts_smul hP.2.1.2.1 _ hci ht`.

Use `choose p hp using hz.1`. Establish `himm : ∀ u b, fderiv ℂ γ (R.A.chart j x) u = torusSmul b (γ (R.A.chart j x)) → u = 0`. Introduce `u b hub`. Establish `hp' : ∀ k, R.lift x x ⟨k, p k⟩ ≠ 0` using `fun k => by`. Rewrite using `[hx]`.

Conclude with `mul_ne_zero (hc k) (hp k)`. Establish `hk` using `R.immersion x (hno _) p hp' j hj`. Establish `hfun : (fun t => affCoord p (R.lift x ((R.A.chart j).symm t))) = affCoord p ∘ γ`. Use function extensionality and compare the values at `t`. Conclude with `(affCoord_torus p _ hci _).symm`.

Rewrite `hk` using `[hfun, fderiv_comp _ (by rw [hγz]; exact differentiableAt_affCoord p z hp) hγA.differentiableAt]`. Establish `: u ∈ (⊥ : Submodule ℂ (Fin e → ℂ))`. Rewrite using `[← hk]`. Use `show fderiv ℂ (affCoord p) (γ (R.A.chart j x)) (fderiv ℂ γ (R.A.chart j x) u) = 0`. Rewrite using `[hub, hγz]`.

Conclude with `fderiv_affCoord_torus p z hp b`. Conclude with `this`. Take `⟨u, b, hub⟩` from `tangent_decomp Ω y e hP hsm γ _ hγA hpts himm w (by rw [hγz]; exact hw)`. Establish `h1` using `levi_torus φ d hhom γ _ hγA (hpts.mono fun t ht => ht.1) (by rw [hγz]; exact hφ z hz.1) u b`. Rewrite `h1` using `[← hub, hγz]`.

Use `show 0 ≤ levi φ z w`. Rewrite using `[h1]`. Establish `hev : φ ∘ γ =ᶠ[𝓝 (R.A.chart j x)] fun t => φ (γ₀ t) + 1 * ((fun _ : Fin e → ℂ => ((∑ k, d k * Real.log ‖(c k)⁻¹‖ : ℝ) : ℂ)) t).re` using `by filter_upwards [h0pts] with t ht`. Simplify using `only [Function.comp_apply, γ]`. Rewrite using `[hhom _ _ hci ht.1, Complex.ofReal_re, one_mul, add_comm]`.

Establish `hc1 : ContDiffAt ℝ 2 (fun t => φ (γ₀ t)) (R.A.chart j x)` using `(hφ _ h0pts.self_of_nhds.1).comp _ (hγ₀A.restrictScalars (𝕜 := ℝ)).contDiffAt`. Rewrite using `[levi_congr hev, levi_add_smul 1 hc1 contDiffAt_const, levi_re_analytic analyticAt_const]`. Simplify using `using hpsh x j hj u`.
-/
theorem levi_nonneg (Ω : Type) [Field Ω] [Algebra ℚ Ω] (y : (Σ k, J k) → Ω) (e : ℕ)
    (hP : IsArithVar (mCoordIdeal y) (e + 1)) (hsm : SmoothGenericFibreM y) {B : Ideal (MRing J)} (hB : B = ⊤)
    (R : AnLogRes (mCoordIdeal y) B e) (φ : ((Σ k, J k) → ℂ) → ℝ) (d : K → ℝ)
    (hhom : ∀ (c : K → ℂ) (z : (Σ k, J k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      φ (torusSmul c z) = ∑ k, d k * Real.log ‖c k‖ + φ z)
    (hφ : ∀ z : (Σ k, J k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ContDiffAt ℝ 2 φ z)
    (hpsh : ∀ x j, x ∈ (R.A.chart j).source → ∀ u,
      0 ≤ levi (fun t => φ (R.lift x ((R.A.chart j).symm t))) (R.A.chart j x) u)
    (z : (Σ k, J k) → ℂ) (hz : z ∈ mcPts (mCoordIdeal y)) (w : (Σ k, J k) → ℂ)
    (hw : IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal y) z w) : 0 ≤ leviForm φ z w := by
  classical
  have hno : ∀ z : (Σ k, J k) → ℂ, z ∉ mcPts B := fun z hz => by
    subst hB
    simpa using hz.2 1 Submodule.mem_top
  obtain ⟨x, c, hc, hx⟩ := R.surj z hz (hno z)
  obtain ⟨j, hj⟩ := R.A.cover x
  let γ₀ : (Fin e → ℂ) → (Σ k, J k) → ℂ := fun t => R.lift x ((R.A.chart j).symm t)
  let γ : (Fin e → ℂ) → (Σ k, J k) → ℂ := fun t => torusSmul (fun k => (c k)⁻¹) (γ₀ t)
  have hci : ∀ k, (c k)⁻¹ ≠ 0 := fun k => inv_ne_zero (hc k)
  have hsx : (R.A.chart j).symm (R.A.chart j x) = x := (R.A.chart j).left_inv hj
  have hmemO : R.A.chart j x ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, hsx]; exact R.mem_U x⟩
  have hO := ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds hmemO
  have hγ₀A : AnalyticAt ℂ γ₀ (R.A.chart j x) := analyticAt_pi_iff.2 fun q => R.holo x q j _ hmemO
  have hγA : AnalyticAt ℂ γ (R.A.chart j x) :=
    analyticAt_pi_iff.2 fun q => analyticAt_const.mul (analyticAt_pi_iff.1 hγ₀A q)
  have hγz : γ (R.A.chart j x) = z := by
    funext q
    simp only [γ, γ₀, torusSmul, hsx, hx]
    rw [← mul_assoc, inv_mul_cancel₀ (hc _), one_mul]
  have h0pts : ∀ᶠ t in 𝓝 (R.A.chart j x), γ₀ t ∈ mcPts (mCoordIdeal y) := by
    filter_upwards [hO] with t ht using R.mem x _ ht.2
  have hpts : ∀ᶠ t in 𝓝 (R.A.chart j x), γ t ∈ mcPts (mCoordIdeal y) := by
    filter_upwards [h0pts] with t ht
    exact mcPts_smul hP.2.1.2.1 _ hci ht
  choose p hp using hz.1
  have himm : ∀ u b, fderiv ℂ γ (R.A.chart j x) u = torusSmul b (γ (R.A.chart j x)) → u = 0 := by
    intro u b hub
    have hp' : ∀ k, R.lift x x ⟨k, p k⟩ ≠ 0 := fun k => by
      rw [hx]; exact mul_ne_zero (hc k) (hp k)
    have hk := R.immersion x (hno _) p hp' j hj
    have hfun : (fun t => affCoord p (R.lift x ((R.A.chart j).symm t))) = affCoord p ∘ γ := by
      funext t
      exact (affCoord_torus p _ hci _).symm
    rw [hfun, fderiv_comp _ (by rw [hγz]; exact differentiableAt_affCoord p z hp) hγA.differentiableAt] at hk
    have : u ∈ (⊥ : Submodule ℂ (Fin e → ℂ)) := by
      rw [← hk]
      show fderiv ℂ (affCoord p) (γ (R.A.chart j x)) (fderiv ℂ γ (R.A.chart j x) u) = 0
      rw [hub, hγz]
      exact fderiv_affCoord_torus p z hp b
    exact this
  obtain ⟨u, b, hub⟩ := tangent_decomp Ω y e hP hsm γ _ hγA hpts himm w (by rw [hγz]; exact hw)
  have h1 := levi_torus φ d hhom γ _ hγA (hpts.mono fun t ht => ht.1) (by rw [hγz]; exact hφ z hz.1) u b
  rw [← hub, hγz] at h1
  show 0 ≤ levi φ z w
  rw [h1]
  have hev : φ ∘ γ =ᶠ[𝓝 (R.A.chart j x)] fun t => φ (γ₀ t) +
      1 * ((fun _ : Fin e → ℂ => ((∑ k, d k * Real.log ‖(c k)⁻¹‖ : ℝ) : ℂ)) t).re := by
    filter_upwards [h0pts] with t ht
    simp only [Function.comp_apply, γ]
    rw [hhom _ _ hci ht.1, Complex.ofReal_re, one_mul, add_comm]
  have hc1 : ContDiffAt ℝ 2 (fun t => φ (γ₀ t)) (R.A.chart j x) :=
    (hφ _ h0pts.self_of_nhds.1).comp _ (hγ₀A.restrictScalars (𝕜 := ℝ)).contDiffAt
  rw [levi_congr hev, levi_add_smul 1 hc1 contDiffAt_const, levi_re_analytic analyticAt_const]
  simpa using hpsh x j hj u

end RootFieldNumerics.Levi

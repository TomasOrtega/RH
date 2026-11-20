import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial Filter Topology

section Alg

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def bsmul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ := fun p => c p.1 * z p

/- English proof (translation)
Rewrite using `[eval_eq', eval_eq', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hm' : m ∈ s.support` using `support_map_subset _ _ hm`. Establish `hblk` using `hs m hm'`. Simplify using `only [bsmul, mul_pow, Finset.prod_mul_distrib]`.

Establish `hc : ∏ p : (Σ k, ι k), c p.1 ^ m p = ∏ k, c k ^ a k`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show ∏ i, c k ^ m ⟨k, i⟩ = c k ^ a k`. Rewrite using `[← hblk k, Finset.prod_pow_eq_pow_sum]`.

Rewrite using `[hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_bsmul_of_isMultiHomog {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) :
    eval (bsmul c z) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval z (map (Int.castRingHom ℂ) s) := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ∈ s.support := support_map_subset _ _ hm
  have hblk := hs m hm'
  simp only [bsmul, mul_pow, Finset.prod_mul_distrib]
  have hc : ∏ p : (Σ k, ι k), c p.1 ^ m p = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ m ⟨k, i⟩ = c k ^ a k
    rw [← hblk k, Finset.prod_pow_eq_pow_sum]
  rw [hc]
  ring

/- English proof (translation)
Unfold `logNorm`. Rewrite using `[eval_bsmul_of_isMultiHomog hs]`. Establish `hh : A.h (bsmul c z) = (∏ k, ‖c k‖ ^ (a k)) * A.h z`. Rewrite using `[show bsmul c z = fun p => c p.1 * z p from rfl, A.smul c z hc]`. Simplify using `[hA, zpow_natCast]`.

Rewrite using `[hh, norm_mul, norm_prod]`. Simplify using `only [norm_pow]`. Rewrite using `[mul_div_mul_left _ _ (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hc k)))]`.
-/
theorem logNorm_bsmul (A : HermLine ι) {s : MRing ι} {a : K → ℕ} (hA : ∀ k, A.a k = a k)
    (hs : IsMultiHomog s a) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    logNorm A s (bsmul c z) = logNorm A s z := by
  unfold logNorm
  rw [eval_bsmul_of_isMultiHomog hs]
  have hh : A.h (bsmul c z) = (∏ k, ‖c k‖ ^ (a k)) * A.h z := by
    rw [show bsmul c z = fun p => c p.1 * z p from rfl, A.smul c z hc]
    simp [hA, zpow_natCast]
  rw [hh, norm_mul, norm_prod]
  simp only [norm_pow]
  rw [mul_div_mul_left _ _ (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hc k)))]

/- English proof (translation)
Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]`. Use `congr 1`. Simplify using the standard rewrite rules. Use `Finset.prod_congr rfl fun k' hk' => ?_` and prove the remaining obligations. Simplify using `[Finset.ne_of_mem_erase hk']`.
-/
theorem prod_update_eq [DecidableEq K] (z : (Σ k, ι k) → ℂ) (i0 : (k : K) → ι k) (k : K) (i : ι k) :
    ∏ k', z ⟨k', Function.update i0 k i k'⟩ = z ⟨k, i⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun k' hk' => ?_
    simp [Finset.ne_of_mem_erase hk']

/- English proof (translation)
Establish `hseg : ∀ i : (k : K) → ι k, ∏ k, z ⟨k, i k⟩ = ∏ k, z' ⟨k, i k⟩` using `fun i => congrFun hs i`. Establish `hP0 : ∏ k, z ⟨k, i0 k⟩ ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => h0 k`. Establish `h0' : ∀ k, z' ⟨k, i0 k⟩ ≠ 0`. Introduce `k`. Establish `h1 : ∏ k, z' ⟨k, i0 k⟩ ≠ 0` using `by rw [← hseg i0]; exact hP0`.

Conclude with `Finset.prod_ne_zero_iff.1 h1 k (Finset.mem_univ _)`. Use `⟨h0', ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `⟨k, i⟩`. Simplify using `only [bsmul]`. Establish `hA' : z ⟨k, i⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ = z' ⟨k, i⟩ * ∏ k' ∈ Finset.univ.erase k, z' ⟨k', i0 k'⟩`.

Rewrite using `[← prod_update_eq z i0 k i, ← prod_update_eq z' i0 k i]`. Conclude with `hseg _`. Establish `hB' : z ⟨k, i0 k⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ = z' ⟨k, i0 k⟩ * ∏ k' ∈ Finset.univ.erase k, z' ⟨k', i0 k'⟩`. Rewrite using `[← prod_update_eq z i0 k (i0 k), ← prod_update_eq z' i0 k (i0 k)]`. Conclude with `hseg _`.

Establish `hP' : ∏ k' ∈ Finset.univ.erase k, z' ⟨k', i0 k'⟩ ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k' _ => h0' k'`. Rewrite using `[div_mul_eq_mul_div, eq_div_iff (h0 k)]`. Apply `mul_right_cancel₀ hP'` to reduce the goal to its premises. Take the linear combination `(-(z ⟨k, i0 k⟩)) * hA' + z ⟨k, i⟩ * hB'`.
-/
theorem eq_bsmul_of_segre_eq {z z' : (Σ k, ι k) → ℂ} (i0 : (k : K) → ι k)
    (h0 : ∀ k, z ⟨k, i0 k⟩ ≠ 0) (hs : segre z = segre z') :
    (∀ k, z' ⟨k, i0 k⟩ ≠ 0) ∧ z' = bsmul (fun k => z' ⟨k, i0 k⟩ / z ⟨k, i0 k⟩) z := by
  classical
  have hseg : ∀ i : (k : K) → ι k, ∏ k, z ⟨k, i k⟩ = ∏ k, z' ⟨k, i k⟩ := fun i => congrFun hs i
  have hP0 : ∏ k, z ⟨k, i0 k⟩ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => h0 k
  have h0' : ∀ k, z' ⟨k, i0 k⟩ ≠ 0 := by
    intro k
    have h1 : ∏ k, z' ⟨k, i0 k⟩ ≠ 0 := by rw [← hseg i0]; exact hP0
    exact Finset.prod_ne_zero_iff.1 h1 k (Finset.mem_univ _)
  refine ⟨h0', ?_⟩
  funext ⟨k, i⟩
  simp only [bsmul]
  have hA' : z ⟨k, i⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ =
      z' ⟨k, i⟩ * ∏ k' ∈ Finset.univ.erase k, z' ⟨k', i0 k'⟩ := by
    rw [← prod_update_eq z i0 k i, ← prod_update_eq z' i0 k i]
    exact hseg _
  have hB' : z ⟨k, i0 k⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ =
      z' ⟨k, i0 k⟩ * ∏ k' ∈ Finset.univ.erase k, z' ⟨k', i0 k'⟩ := by
    rw [← prod_update_eq z i0 k (i0 k), ← prod_update_eq z' i0 k (i0 k)]
    exact hseg _
  have hP' : ∏ k' ∈ Finset.univ.erase k, z' ⟨k', i0 k'⟩ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => h0' k'
  rw [div_mul_eq_mul_div, eq_div_iff (h0 k)]
  apply mul_right_cancel₀ hP'
  linear_combination (-(z ⟨k, i0 k⟩)) * hA' + z ⟨k, i⟩ * hB'

end Alg

section Hess

variable {e : ℕ}

/- English proof (translation)
Establish `hd : HasFDerivAt (fun y' => (h y').re) (Complex.reCLM.comp ((fderiv ℂ h y).restrictScalars ℝ)) y` using `Complex.reCLM.hasFDerivAt.comp y (hh.hasFDerivAt.restrictScalars ℝ)`. Rewrite using `[hd.fderiv]`. Both sides reduce to the same expression.
-/
theorem fderiv_re_apply {h : (Fin e → ℂ) → ℂ} {y : Fin e → ℂ} (hh : DifferentiableAt ℂ h y)
    (v : Fin e → ℂ) : fderiv ℝ (fun y' => (h y').re) y v = (fderiv ℂ h y v).re := by
  have hd : HasFDerivAt (fun y' => (h y').re)
      (Complex.reCLM.comp ((fderiv ℂ h y).restrictScalars ℝ)) y :=
    Complex.reCLM.hasFDerivAt.comp y (hh.hasFDerivAt.restrictScalars ℝ)
  rw [hd.fderiv]
  rfl

/- English proof (translation)
Set `Φ : ((Fin e → ℂ) →L[ℂ] ℂ) →L[ℝ] ((Fin e → ℂ) →L[ℝ] ℝ)` to `(ContinuousLinearMap.compL ℝ (Fin e → ℂ) ℂ ℝ Complex.reCLM).comp (ContinuousLinearMap.restrictScalarsL ℂ (Fin e → ℂ) ℂ ℝ ℝ)`. Establish `hΦ : ∀ L : (Fin e → ℂ) →L[ℂ] ℂ, ∀ u, Φ L u = (L u).re` using `fun L u => rfl`. Establish `heq : fderiv ℝ (fun y' => (G y').re) =ᶠ[𝓝 y] fun y' => Φ (fderiv ℂ G y')` using `by filter_upwards [hG.eventually_analyticAt] with y' hy'`. Use extensionality with `u`. Rewrite using `[fderiv_re_apply hy'.differentiableAt u, hΦ]`.

Establish `hD : HasFDerivAt (fderiv ℂ G) (fderiv ℂ (fderiv ℂ G) y) y` using `hG.fderiv.differentiableAt.hasFDerivAt`. Establish `h2 : HasFDerivAt (fun y' => Φ (fderiv ℂ G y')) (Φ.comp ((fderiv ℂ (fderiv ℂ G) y).restrictScalars ℝ)) y` using `Φ.hasFDerivAt.comp y (hD.restrictScalars ℝ)`. Rewrite using `[heq.fderiv_eq, h2.fderiv]`. Both sides reduce to the same expression.
-/
theorem hess_re {G : (Fin e → ℂ) → ℂ} {y : Fin e → ℂ} (hG : AnalyticAt ℂ G y) (v w : Fin e → ℂ) :
    fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y v w = (fderiv ℂ (fderiv ℂ G) y v w).re := by
  let Φ : ((Fin e → ℂ) →L[ℂ] ℂ) →L[ℝ] ((Fin e → ℂ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (Fin e → ℂ) ℂ ℝ Complex.reCLM).comp
      (ContinuousLinearMap.restrictScalarsL ℂ (Fin e → ℂ) ℂ ℝ ℝ)
  have hΦ : ∀ L : (Fin e → ℂ) →L[ℂ] ℂ, ∀ u, Φ L u = (L u).re := fun L u => rfl
  have heq : fderiv ℝ (fun y' => (G y').re) =ᶠ[𝓝 y] fun y' => Φ (fderiv ℂ G y') := by
    filter_upwards [hG.eventually_analyticAt] with y' hy'
    ext u
    rw [fderiv_re_apply hy'.differentiableAt u, hΦ]
  have hD : HasFDerivAt (fderiv ℂ G) (fderiv ℂ (fderiv ℂ G) y) y :=
    hG.fderiv.differentiableAt.hasFDerivAt
  have h2 : HasFDerivAt (fun y' => Φ (fderiv ℂ G y'))
      (Φ.comp ((fderiv ℂ (fderiv ℂ G) y).restrictScalars ℝ)) y :=
    Φ.hasFDerivAt.comp y (hD.restrictScalars ℝ)
  rw [heq.fderiv_eq, h2.fderiv]
  rfl

/- English proof (translation)
Establish `hre2 : ContDiffAt ℝ 2 (fun y' => (G y').re) y` using `Complex.reCLM.contDiff.contDiffAt.comp y (hG.contDiffAt.restrict_scalars ℝ)`. Establish `hφev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ φ y'` using `(hφ.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num)`. Establish `hreev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ (fun y' => (G y').re) y'` using `(hre2.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num)`. Establish `heq : fderiv ℝ (fun y' => φ y' + (G y').re + C) =ᶠ[𝓝 y] fun y' => fderiv ℝ φ y' + fderiv ℝ (fun y' => (G y').re) y'` using `by filter_upwards [hφev, hreev] with y' h1 h2`. Rewrite using `[fderiv_add_const]`.

Conclude with `(h1.hasFDerivAt.add h2.hasFDerivAt).fderiv`. Establish `hdφ : DifferentiableAt ℝ (fderiv ℝ φ) y` using `(hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`. Establish `hdre : DifferentiableAt ℝ (fderiv ℝ (fun y' => (G y').re)) y` using `(hre2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`. Establish `hsum : fderiv ℝ (fderiv ℝ (fun y' => φ y' + (G y').re + C)) y = fderiv ℝ (fderiv ℝ φ) y + fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y`. Rewrite using `[heq.fderiv_eq]`.

Conclude with `(hdφ.hasFDerivAt.add hdre.hasFDerivAt).fderiv`. Establish `hH` using `hess_re hG`. Establish `k1 : ∀ u v, fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y (Complex.I • u) (Complex.I • v) = - fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y u v`. Introduce `u v`. Rewrite using `[hH, hH]`.

Simplify using `[map_smul, ← mul_assoc]`. Establish `k2 : ∀ u v, fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y u (Complex.I • v) = fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y (Complex.I • u) v`. Introduce `u v`. Rewrite using `[hH, hH]`. Simplify using `[map_smul]`.

Use extensionality with `i j`. Simplify using `only [cxHessian, hsum, ContinuousLinearMap.add_apply, k1, k2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cxHessian_add_re {φ : (Fin e → ℂ) → ℝ} {G : (Fin e → ℂ) → ℂ} {y : Fin e → ℂ} (C : ℝ)
    (hφ : ContDiffAt ℝ 2 φ y) (hG : AnalyticAt ℂ G y) :
    cxHessian (fun y' => φ y' + (G y').re + C) y = cxHessian φ y := by
  have hre2 : ContDiffAt ℝ 2 (fun y' => (G y').re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y (hG.contDiffAt.restrict_scalars ℝ)
  have hφev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ φ y' :=
    (hφ.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num)
  have hreev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ (fun y' => (G y').re) y' :=
    (hre2.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num)
  have heq : fderiv ℝ (fun y' => φ y' + (G y').re + C) =ᶠ[𝓝 y]
      fun y' => fderiv ℝ φ y' + fderiv ℝ (fun y' => (G y').re) y' := by
    filter_upwards [hφev, hreev] with y' h1 h2
    rw [fderiv_add_const]
    exact (h1.hasFDerivAt.add h2.hasFDerivAt).fderiv
  have hdφ : DifferentiableAt ℝ (fderiv ℝ φ) y :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdre : DifferentiableAt ℝ (fderiv ℝ (fun y' => (G y').re)) y :=
    (hre2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsum : fderiv ℝ (fderiv ℝ (fun y' => φ y' + (G y').re + C)) y =
      fderiv ℝ (fderiv ℝ φ) y + fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y := by
    rw [heq.fderiv_eq]
    exact (hdφ.hasFDerivAt.add hdre.hasFDerivAt).fderiv
  have hH := hess_re hG
  have k1 : ∀ u v, fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y (Complex.I • u) (Complex.I • v) =
      - fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y u v := by
    intro u v
    rw [hH, hH]
    simp [map_smul, ← mul_assoc]
  have k2 : ∀ u v, fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y u (Complex.I • v) =
      fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y (Complex.I • u) v := by
    intro u v
    rw [hH, hH]
    simp [map_smul]
  ext i j
  simp only [cxHessian, hsum, ContinuousLinearMap.add_apply, k1, k2]
  push_cast
  ring

/- English proof (translation)
Establish `h2 : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ g) y` using `h.fderiv.fderiv_eq`. Unfold `cxHessian`. Rewrite using `[h2]`.
-/
theorem cxHessian_congr {f g : (Fin e → ℂ) → ℝ} {y : Fin e → ℂ} (h : f =ᶠ[𝓝 y] g) :
    cxHessian f y = cxHessian g y := by
  have h2 : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ g) y := h.fderiv.fderiv_eq
  unfold cxHessian
  rw [h2]

end Hess

end ReciprocityTheory.ChartRestriction.G.Geo

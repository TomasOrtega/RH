import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AInterpSt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CasChainA

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Topology ContDiff

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

/- English proof (translation)
Rewrite using `[add_comm]`. Conclude with `ReciprocityTheory.AnForm.A.det_smul_add_smul_eq_sum_mdisc t (1 - t) M₁ M₀`.
-/
theorem det_interp (M₀ M₁ : Matrix (Fin D) (Fin D) ℂ) (t : ℂ) :
    ((1 - t) • M₀ + t • M₁).det = ∑ i ∈ Finset.range (D + 1),
      (D.choose i : ℂ) * t ^ i * (1 - t) ^ (D - i) *
        mixedDisc (fun j : Fin D => if j.val < i then M₁ else M₀) := by
  rw [add_comm]
  exact ReciprocityTheory.AnForm.A.det_smul_add_smul_eq_sum_mdisc t (1 - t) M₁ M₀

/- English proof (translation)
Establish `hd : fderiv ℝ ψ =ᶠ[𝓝 y] fun y' => s • fderiv ℝ a y' + u • fderiv ℝ b y'` using `by filter_upwards [hψ.eventuallyEq_nhds, ha, hb] with y' h1 h2 h3`. Rewrite using `[h1.fderiv_eq]`. Establish `d2` using `h2.differentiableAt (by norm_num)`. Establish `d3` using `h3.differentiableAt (by norm_num)`. Conclude with `((d2.hasFDerivAt.const_mul s).add (d3.hasFDerivAt.const_mul u)).fderiv`.

Establish `hH : fderiv ℝ (fderiv ℝ ψ) y = s • fderiv ℝ (fderiv ℝ a) y + u • fderiv ℝ (fderiv ℝ b) y`. Rewrite using `[hd.fderiv_eq]`. Establish `d2` using `(ha.self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`. Establish `d3` using `(hb.self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`. Conclude with `((d2.hasFDerivAt.const_smul s).add (d3.hasFDerivAt.const_smul u)).fderiv`.

Use extensionality with `i j`. Simplify using `only [cxHessian, hH, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.smul_apply]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gaamix_cxHessian_comb {a b ψ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (s u : ℝ)
    (ha : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 a y') (hb : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 b y')
    (hψ : ψ =ᶠ[𝓝 y] fun y' => s * a y' + u * b y') :
    cxHessian ψ y = (s : ℂ) • cxHessian a y + (u : ℂ) • cxHessian b y := by
  have hd : fderiv ℝ ψ =ᶠ[𝓝 y] fun y' => s • fderiv ℝ a y' + u • fderiv ℝ b y' := by
    filter_upwards [hψ.eventuallyEq_nhds, ha, hb] with y' h1 h2 h3
    rw [h1.fderiv_eq]
    have d2 := h2.differentiableAt (by norm_num)
    have d3 := h3.differentiableAt (by norm_num)
    exact ((d2.hasFDerivAt.const_mul s).add (d3.hasFDerivAt.const_mul u)).fderiv
  have hH : fderiv ℝ (fderiv ℝ ψ) y =
      s • fderiv ℝ (fderiv ℝ a) y + u • fderiv ℝ (fderiv ℝ b) y := by
    rw [hd.fderiv_eq]
    have d2 := (ha.self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have d3 := (hb.self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    exact ((d2.hasFDerivAt.const_smul s).add (d3.hasFDerivAt.const_smul u)).fderiv
  ext i j
  simp only [cxHessian, hH, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.smul_apply]
  push_cast
  ring

/- English proof (translation)
Take `⟨i, hi⟩` from `hz.1 ()`. Introduce and unpack `rfl`. Conclude with `hi rfl`.
-/
theorem gaamix_ne_zero_of_mcPts {P : Ideal (MRing (GlobalTheory κ))} {z : Ix κ → ℂ} (hz : z ∈ mcPts P) :
    z ≠ 0 := by
  obtain ⟨i, hi⟩ := hz.1 ()
  rintro rfl
  exact hi rfl

/- English proof (translation)
Take `⟨U, hU, hUo, hyU⟩` from `eventually_nhds_iff.mp hγ`. Establish `hdU : DifferentiableOn ℂ γ U` using `fun y' h => (hU y' h).differentiableWithinAt`. Establish `hc : ContDiffAt ℝ ∞ γ y` using `((ReciprocityTheory.ChartRestriction.DS.S7.cca_contDiffOn hUo hdU).contDiffAt (hUo.mem_nhds hyU)).restrict_scalars ℝ`. Establish `hρ : ContDiffAt ℝ ∞ m.ρ (γ y)` using `hm.contDiffAt (isOpen_ne.mem_nhds hy)`. Conclude with `(contDiffAt_infty.mp ((hρ.comp y hc).log (m.pos _ hy).ne')) 2` after adjusting the coercions.
-/
theorem gaamix_contDiffAt_log {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m)
    {γ : (Fin D → ℂ) → Ix κ → ℂ} {y : Fin D → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y') (hy : γ y ≠ 0) :
    ContDiffAt ℝ 2 (fun y' => Real.log (m.ρ (γ y'))) y := by
  obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.mp hγ
  have hdU : DifferentiableOn ℂ γ U := fun y' h => (hU y' h).differentiableWithinAt
  have hc : ContDiffAt ℝ ∞ γ y :=
    ((ReciprocityTheory.ChartRestriction.DS.S7.cca_contDiffOn hUo hdU).contDiffAt (hUo.mem_nhds hyU)).restrict_scalars ℝ
  have hρ : ContDiffAt ℝ ∞ m.ρ (γ y) :=
    hm.contDiffAt (isOpen_ne.mem_nhds hy)
  exact_mod_cast (contDiffAt_infty.mp ((hρ.comp y hc).log (m.pos _ hy).ne')) 2

/- English proof (translation)
Establish `h₀` using `m₀.pos z hz`. Establish `h₁` using `m₁.pos z hz`. Use `show Real.log (m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t) = _`. Rewrite using `[Real.log_mul (Real.rpow_pos_of_pos h₀ _).ne' (Real.rpow_pos_of_pos h₁ _).ne', Real.log_rpow h₀, Real.log_rpow h₁]`.
-/
theorem gaamix_log_interp (m₀ m₁ : ConeMetric ℂ (Ix κ)) (t : ℝ) {z : Ix κ → ℂ} (hz : z ≠ 0) :
    Real.log ((interp m₀ m₁ t).ρ z) = (1 - t) * Real.log (m₀.ρ z) + t * Real.log (m₁.ρ z) := by
  have h₀ := m₀.pos z hz
  have h₁ := m₁.pos z hz
  show Real.log (m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t) = _
  rw [Real.log_mul (Real.rpow_pos_of_pos h₀ _).ne' (Real.rpow_pos_of_pos h₁ _).ne',
    Real.log_rpow h₀, Real.log_rpow h₁]

/- English proof (translation)
Establish `hev : ∀ᶠ y' in 𝓝 y, ∀ᶠ y'' in 𝓝 y', DifferentiableAt ℂ γ y'' ∧ γ y'' ≠ 0` using `hγ.eventually_nhds`. Establish `ha : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (m₀.ρ (γ y''))) y'` using `by filter_upwards [hev] with y' hy'`. Conclude with `gaamix_contDiffAt_log h₀ (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2`. Establish `hb : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (m₁.ρ (γ y''))) y'` using `by filter_upwards [hev] with y' hy'`. Conclude with `gaamix_contDiffAt_log h₁ (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2`.

Establish `hψ : (fun y' => Real.log ((interp m₀ m₁ t).ρ (γ y'))) =ᶠ[𝓝 y] fun y' => (1 - t) * Real.log (m₀.ρ (γ y')) + t * Real.log (m₁.ρ (γ y'))` using `by filter_upwards [hγ] with y' hy'`. Conclude with `gaamix_log_interp m₀ m₁ t hy'.2`. Establish `hH` using `gaamix_cxHessian_comb (1 - t) t ha hb hψ`. Use `set H₀ := cxHessian (fun y'' => Real.log (m₀.ρ (γ y''))) y`. Use `set H₁ := cxHessian (fun y'' => Real.log (m₁.ρ (γ y''))) y`.

Establish `hmix : ∀ i, (fun k => cxHessian (fun y' => mixPot m₀ m₁ D i k (γ y')) y) = fun j : Fin D => if j.val < i then H₁ else H₀`. Introduce `i`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k.val < i`. Simplify using `only [mixPot, hk, if_true]`.

Both sides reduce to the same expression. Simplify using `only [mixPot, hk, if_false]`. Both sides reduce to the same expression. Establish `hpure : (fun k => cxHessian (fun y' => purePot (interp m₀ m₁ t) D k (γ y')) y) = fun _ => (1 - (t : ℂ)) • H₀ + (t : ℂ) • H₁`. Use function extensionality and compare the values at `k`.

Use `show cxHessian (fun y' => Real.log ((interp m₀ m₁ t).ρ (γ y'))) y = _`. Rewrite using `[hH]`. Use `push_cast`. Both sides reduce to the same expression. Simplify using `only [maDensity]`.

Establish `hc : mixedDisc (fun _ : Fin D => (1 - (t : ℂ)) • H₀ + (t : ℂ) • H₁) = ((1 - (t : ℂ)) • H₀ + (t : ℂ) • H₁).det` using `ReciprocityTheory.AnForm.A.mdisc_const _`. Rewrite using `[hpure, hc, det_interp, Complex.re_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hmix i]`. Establish `e : (D.choose i : ℂ) * (t : ℂ) ^ i * (1 - (t : ℂ)) ^ (D - i) = ((D.choose i * t ^ i * (1 - t) ^ (D - i) : ℝ) : ℂ)` using `by push_cast; ring`.

Rewrite using `[e, Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gbamix_maDensity_interp {m₀ m₁ : ConeMetric ℂ (Ix κ)} (h₀ : IsSmoothMetric m₀)
    (h₁ : IsSmoothMetric m₁) (t : ℝ) {γ : (Fin D → ℂ) → Ix κ → ℂ} {y : Fin D → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ γ y' ≠ 0) :
    maDensity (fun j y' => purePot (interp m₀ m₁ t) D j (γ y')) y =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
        maDensity (fun j y' => mixPot m₀ m₁ D i j (γ y')) y := by
  have hev : ∀ᶠ y' in 𝓝 y, ∀ᶠ y'' in 𝓝 y', DifferentiableAt ℂ γ y'' ∧ γ y'' ≠ 0 :=
    hγ.eventually_nhds
  have ha : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (m₀.ρ (γ y''))) y' := by
    filter_upwards [hev] with y' hy'
    exact gaamix_contDiffAt_log h₀ (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hb : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (m₁.ρ (γ y''))) y' := by
    filter_upwards [hev] with y' hy'
    exact gaamix_contDiffAt_log h₁ (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hψ : (fun y' => Real.log ((interp m₀ m₁ t).ρ (γ y'))) =ᶠ[𝓝 y]
      fun y' => (1 - t) * Real.log (m₀.ρ (γ y')) + t * Real.log (m₁.ρ (γ y')) := by
    filter_upwards [hγ] with y' hy'
    exact gaamix_log_interp m₀ m₁ t hy'.2
  have hH := gaamix_cxHessian_comb (1 - t) t ha hb hψ
  set H₀ := cxHessian (fun y'' => Real.log (m₀.ρ (γ y''))) y
  set H₁ := cxHessian (fun y'' => Real.log (m₁.ρ (γ y''))) y
  have hmix : ∀ i, (fun k => cxHessian (fun y' => mixPot m₀ m₁ D i k (γ y')) y) =
      fun j : Fin D => if j.val < i then H₁ else H₀ := by
    intro i
    funext k
    by_cases hk : k.val < i
    · simp only [mixPot, hk, if_true]; rfl
    · simp only [mixPot, hk, if_false]; rfl
  have hpure : (fun k => cxHessian (fun y' => purePot (interp m₀ m₁ t) D k (γ y')) y) =
      fun _ => (1 - (t : ℂ)) • H₀ + (t : ℂ) • H₁ := by
    funext k
    show cxHessian (fun y' => Real.log ((interp m₀ m₁ t).ρ (γ y'))) y = _
    rw [hH]
    push_cast
    rfl
  simp only [maDensity]
  have hc : mixedDisc (fun _ : Fin D => (1 - (t : ℂ)) • H₀ + (t : ℂ) • H₁) =
      ((1 - (t : ℂ)) • H₀ + (t : ℂ) • H₁).det := ReciprocityTheory.AnForm.A.mdisc_const _
  rw [hpure, hc, det_interp, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hmix i]
  have e : (D.choose i : ℂ) * (t : ℂ) ^ i * (1 - (t : ℂ)) ^ (D - i) =
      ((D.choose i * t ^ i * (1 - t) ^ (D - i) : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.re_ofReal_mul]
  ring

/- English proof (translation)
Take `⟨i, hi⟩` from `hz ()`. Introduce and unpack `rfl`. Conclude with `hi rfl`.
-/
theorem gbamix_ne_zero_of_blocks {z : Ix κ → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : z ≠ 0 := by
  obtain ⟨i, hi⟩ := hz ()
  rintro rfl
  exact hi rfl

/- English proof (translation)
Conclude with `(show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m.ρ {z | z ≠ 0} from hm).mono fun z hz => gbamix_ne_zero_of_blocks hz`.
-/
theorem gbamix_smoothHerm_ofCone {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m) :
    IsSmoothHerm (HermLine.ofCone m) := by
  exact (show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m.ρ {z | z ≠ 0} from hm).mono
    fun z hz => gbamix_ne_zero_of_blocks hz

/- English proof (translation)
Establish `e : (fun p : Ix κ => c p.1 * z p) = c () • z`. Use function extensionality and compare the values at `p`. Both sides reduce to the same expression. Unfold `logRatio`. Rewrite using `[e, m₀.smul, m₁.smul, mul_div_mul_left _ _ (norm_ne_zero_iff.2 (hc ()))]`.
-/
theorem gbamix_logRatio_deg {m₀ m₁ : ConeMetric ℂ (Ix κ)} (c : Unit → ℂ) (z : Ix κ → ℂ)
    (hc : ∀ k, c k ≠ 0) : logRatio m₀ m₁ (fun p => c p.1 * z p) = logRatio m₀ m₁ z := by
  have e : (fun p : Ix κ => c p.1 * z p) = c () • z := by
    funext p
    rfl
  unfold logRatio
  rw [e, m₀.smul, m₁.smul, mul_div_mul_left _ _ (norm_ne_zero_iff.2 (hc ()))]

/- English proof (translation)
Establish `h0 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₀.ρ {z | z ≠ 0}` using `h₀`. Establish `h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₁.ρ {z | z ≠ 0}` using `h₁`. Use `show ContDiffOn ℝ _ (fun z => Real.log (m₁.ρ z / m₀.ρ z)) {z | z ≠ 0}`. Conclude with `(h1.div h0 fun z hz => (m₀.pos z hz).ne').log fun z hz => (div_pos (m₁.pos z hz) (m₀.pos z hz)).ne'`.
-/
theorem gbamix_smooth_logRatio {m₀ m₁ : ConeMetric ℂ (Ix κ)} (h₀ : IsSmoothMetric m₀)
    (h₁ : IsSmoothMetric m₁) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (logRatio m₀ m₁) {z | z ≠ 0} := by
  have h0 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₀.ρ {z | z ≠ 0} := h₀
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₁.ρ {z | z ≠ 0} := h₁
  show ContDiffOn ℝ _ (fun z => Real.log (m₁.ρ z / m₀.ρ z)) {z | z ≠ 0}
  exact (h1.div h0 fun z hz => (m₀.pos z hz).ne').log fun z hz =>
    (div_pos (m₁.pos z hz) (m₀.pos z hz)).ne'

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

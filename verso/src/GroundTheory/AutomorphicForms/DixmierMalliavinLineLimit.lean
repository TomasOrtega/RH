import Mathlib

namespace GroundTheory.Automorphic

open MeasureTheory Filter Topology Set
open scoped FourierTransform ContDiff

namespace WeakLimit

/- English proof (translation)
Simplify using `using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner hf hg)`.
-/
theorem integral_fourier_mul_eq {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕 f ξ * g ξ = ∫ x, f x * 𝓕 g x := by
  simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner hf hg)

/- English proof (translation)
Rewrite using `[Real.fourierInv_eq_fourier_comp_neg, integral_fourier_mul_eq hf.comp_neg hg, ← integral_neg_eq_self (fun x => f x * 𝓕⁻ g x)]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `[Real.fourierInv_eq_fourier_neg]`.
-/
theorem integral_fourierInv_mul_eq {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕⁻ f ξ * g ξ = ∫ x, f x * 𝓕⁻ g x := by
  rw [Real.fourierInv_eq_fourier_comp_neg, integral_fourier_mul_eq hf.comp_neg hg,
    ← integral_neg_eq_self (fun x => f x * 𝓕⁻ g x)]
  congr 1; funext x
  simp [Real.fourierInv_eq_fourier_neg]

/- English proof (translation)
The claim follows from `VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _`.
-/
theorem norm_fourier_le (f : ℝ → ℂ) (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ ∫ x, ‖f x‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

/- English proof (translation)
The claim follows from `VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf`.
-/
theorem continuous_fourier_of_integrable {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf

/- English proof (translation)
Take `⟨p, hp⟩` from `exists_polynomial_near_of_continuousOn a b (fun t => (ψ t).re) (Complex.continuous_re.comp hψ).continuousOn (η / 2) (by positivity)`. Take `⟨q, hq⟩` from `exists_polynomial_near_of_continuousOn a b (fun t => (ψ t).im) (Complex.continuous_im.comp hψ).continuousOn (η / 2) (by positivity)`. Establish `hpd : ∀ r : Polynomial ℝ, ContDiff ℝ ∞ (fun t : ℝ => r.eval t)` using `fun r => by`. Simplify `r.contDiff_aeval (𝕜 := ℝ) ∞` using `[Polynomial.coe_aeval_eq_eval]`. Set `χ : ContDiffBump ((a + b) / 2)` to `⟨|b - a| + 1, |b - a| + 2, by positivity, by linarith⟩`.

Use `⟨fun t => (χ t : ℂ) * (((p.eval t : ℝ) : ℂ) + ((q.eval t : ℝ) : ℂ) * Complex.I), ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Complex.ofRealCLM.contDiff.comp χ.contDiff).mul ((Complex.ofRealCLM.contDiff.comp (hpd p)).add ((Complex.ofRealCLM.contDiff.comp (hpd q)).mul contDiff_const))`. Conclude with `(χ.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right`. Introduce `t ht`. Establish `hχ : χ t = 1`.

Apply `χ.one_of_mem_closedBall` to reduce the goal to its premises. Rewrite using `[Metric.mem_closedBall, Real.dist_eq]`. Use `ht.1` as an intermediate fact. Use `ht.2` as an intermediate fact. Apply the tactic sequence `rw [abs_le]; constructor <;> cases abs_cases (b - a) <;> linarith`.

Use `show ‖ψ t - (χ t : ℂ) * _‖ ≤ η`. Rewrite using `[hχ, Complex.ofReal_one, one_mul]`. Use `(Complex.norm_le_abs_re_add_abs_im _).trans ?_` and prove the remaining obligations. Establish `h1` using `hp t ht`. Establish `h2` using `hq t ht`.

Simplify using `only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.add_im, Complex.mul_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]`. Rewrite `h1`, `h2` using `[abs_sub_comm]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_smooth_near (a b : ℝ) {ψ : ℝ → ℂ} (hψ : Continuous ψ) {η : ℝ} (hη : 0 < η) :
    ∃ ψ' : ℝ → ℂ, ContDiff ℝ ∞ ψ' ∧ HasCompactSupport ψ' ∧ ∀ t ∈ Icc a b, ‖ψ t - ψ' t‖ ≤ η := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b (fun t => (ψ t).re)
    (Complex.continuous_re.comp hψ).continuousOn (η / 2) (by positivity)
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn a b (fun t => (ψ t).im)
    (Complex.continuous_im.comp hψ).continuousOn (η / 2) (by positivity)
  have hpd : ∀ r : Polynomial ℝ, ContDiff ℝ ∞ (fun t : ℝ => r.eval t) := fun r => by
    simpa [Polynomial.coe_aeval_eq_eval] using r.contDiff_aeval (𝕜 := ℝ) ∞
  let χ : ContDiffBump ((a + b) / 2) := ⟨|b - a| + 1, |b - a| + 2, by positivity, by linarith⟩
  refine ⟨fun t => (χ t : ℂ) * (((p.eval t : ℝ) : ℂ) + ((q.eval t : ℝ) : ℂ) * Complex.I), ?_, ?_, ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp χ.contDiff).mul
      ((Complex.ofRealCLM.contDiff.comp (hpd p)).add
        ((Complex.ofRealCLM.contDiff.comp (hpd q)).mul contDiff_const))
  · exact (χ.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  · intro t ht
    have hχ : χ t = 1 := by
      apply χ.one_of_mem_closedBall
      rw [Metric.mem_closedBall, Real.dist_eq]
      have := ht.1; have := ht.2
      rw [abs_le]; constructor <;> cases abs_cases (b - a) <;> linarith
    show ‖ψ t - (χ t : ℂ) * _‖ ≤ η
    rw [hχ, Complex.ofReal_one, one_mul]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have h1 := hp t ht
    have h2 := hq t ht
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.add_im, Complex.mul_im, mul_zero,
      mul_one, sub_zero, add_zero, zero_add]
    rw [abs_sub_comm] at h1 h2
    linarith

end WeakLimit

/- English proof (translation)
Use `set Kc : ℕ → ℝ → ℂ := fun N t => (K N t : ℂ) with hKc`. Establish `hKci : ∀ N, Integrable (Kc N)` using `fun N => (hKi N).ofReal`. Establish `hKn : ∀ N ξ, ‖𝓕 (Kc N) ξ‖ ≤ 1`. Introduce `N ξ`. Use `(WeakLimit.norm_fourier_le _ ξ).trans ?_` and prove the remaining obligations.

Simplify using `only [Kc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK0 N _)]`. Conclude with `hK1 N`. Use `choose Φ hΦ using hconv`. Establish `hΦd : ∀ m : ℕ, ∃ C, ∀ ξ, ‖Φ ξ‖ ≤ C * (1 + |ξ|) ^ (-(m : ℝ))`. Introduce `m`.

Take `⟨C, N₀, hC⟩` from `hdecay m`. Conclude with `⟨C, fun ξ => le_of_tendsto ((hΦ ξ).norm) (eventually_atTop.2 ⟨N₀, fun N hN => hC N hN ξ⟩)⟩`. Establish `hΦm : AEStronglyMeasurable Φ` using `aestronglyMeasurable_of_tendsto_ae atTop (fun N => (WeakLimit.continuous_fourier_of_integrable (hKci N)).aestronglyMeasurable) (ae_of_all _ hΦ)`. Establish `hΦint : ∀ n : ℕ, Integrable (fun ξ : ℝ => ‖ξ‖ ^ n * ‖Φ ξ‖)`. Introduce `n`.

Take `⟨C, hC⟩` from `hΦd (n + 2)`. Establish `hI : Integrable (fun ξ : ℝ => C * (1 + ‖ξ‖) ^ (-(2 : ℝ)))` using `(integrable_one_add_norm (by norm_num)).const_mul C`. Use `hI.mono' ((continuous_norm.pow n).aestronglyMeasurable.mul hΦm.norm) (ae_of_all _ fun ξ => ?_)` and prove the remaining obligations. Establish `h1 : 0 < 1 + |ξ|` using `by positivity`. Rewrite using `[norm_mul, norm_pow, norm_norm, norm_norm, Real.norm_eq_abs]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add h1]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hΦi : Integrable Φ` using `(integrable_norm_iff hΦm).1 (by simpa using hΦint 0)`. Use `set g : ℝ → ℂ := 𝓕⁻ Φ with hgdef`. Establish `hg : ContDiff ℝ ∞ g`. Rewrite using `[hgdef, Real.fourierInv_eq_fourier_comp_neg]`. Conclude with `Real.contDiff_fourier fun n _ => by simpa using (hΦint n).comp_neg`.

Establish `hsmooth : ∀ ψ : ℝ → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → Tendsto (fun N => ∫ t, ψ t * Kc N t) atTop (𝓝 (∫ t, ψ t * g t))`. Introduce `ψ hψ hψc`. Set `ψS` to `hψc.toSchwartzMap hψ`. Establish `hψi : Integrable ψ` using `hψ.continuous.integrable_of_hasCompactSupport hψc`. Establish `hθi : Integrable (𝓕⁻ ψ)`.

Use `(𝓕⁻ ψS).integrable (μ := volume)` as an intermediate fact. Rewrite `this` using `[SchwartzMap.fourierInv_coe]`. Then use the resulting hypothesis. Establish `hFψ : Integrable (𝓕 ψ)`. Use `(𝓕 ψS).integrable (μ := volume)` as an intermediate fact. Rewrite `this` using `[SchwartzMap.fourier_coe]`. Then use the resulting hypothesis.

Establish `hinv : 𝓕 (𝓕⁻ ψ) = ψ` using `hψ.continuous.fourier_fourierInv_eq hψi hFψ`. Establish `e1 : ∀ N, ∫ t, ψ t * Kc N t = ∫ ξ, 𝓕⁻ ψ ξ * 𝓕 (Kc N) ξ`. Introduce `N`. Use `conv_lhs => rw [← hinv]`. Conclude with `WeakLimit.integral_fourier_mul_eq hθi (hKci N)`.

Establish `e2 : ∫ t, ψ t * g t = ∫ ξ, 𝓕⁻ ψ ξ * Φ ξ` using `(WeakLimit.integral_fourierInv_mul_eq hψi hΦi).symm`. Repeatedly rewrite using `[e1, e2]`. Use `tendsto_integral_of_dominated_convergence (fun ξ => ‖𝓕⁻ ψ ξ‖) (fun N => ?_) hθi.norm (fun N => ae_of_all _ fun ξ => ?_) (ae_of_all _ fun ξ => (hΦ ξ).const_mul _)` and prove the remaining obligations. Conclude with `hθi.aestronglyMeasurable.mul (WeakLimit.continuous_fourier_of_integrable (hKci N)).aestronglyMeasurable`. Rewrite using `[norm_mul]`.

Conclude with `mul_le_of_le_one_right (norm_nonneg _) (hKn N ξ)`. Establish `hgi : LocallyIntegrable g` using `hg.continuous.locallyIntegrable`. Establish `hsupp : Function.support g ⊆ Icc a b`. Establish `hae : ∀ᵐ x, x ∈ (Icc a b)ᶜ → g x = 0`. Use `isClosed_Icc.isOpen_compl.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hgi.locallyIntegrableOn _) fun φ hφ hφc hφs => ?_` and prove the remaining obligations.

Establish `hlim` using `hsmooth (fun x => (φ x : ℂ)) (Complex.ofRealCLM.contDiff.comp hφ) (hφc.comp_left Complex.ofReal_zero)`. Establish `h0 : ∀ N, ∫ t, (φ t : ℂ) * Kc N t = 0`. Introduce `N`. Use `integral_eq_zero_of_ae (ae_of_all _ fun t => ?_)` and prove the remaining obligations. Distinguish the cases in `ht : t ∈ Icc a b`.

Establish `: φ t = 0` using `image_eq_zero_of_notMem_tsupport fun h' => hφs h' ht`. Simplify using `[this]`. Establish `: K N t = 0` using `Function.notMem_support.1 fun h' => ht (hKs N h')`. Simplify using `[Kc, this]`. Rewrite `hlim` using `[h0]`.

Repeatedly rewrite using `[Complex.real_smul]`. Conclude with `tendsto_nhds_unique hlim tendsto_const_nhds`. Introduce `x hx`. Assume the negation of the conclusion as `hxI`. Establish `hopen : IsOpen ((Icc a b)ᶜ ∩ Function.support g)` using `isClosed_Icc.isOpen_compl.inter hg.continuous.isOpen_support`.

Establish `hnull : volume ((Icc a b)ᶜ ∩ Function.support g) = 0`. Rewrite using `[measure_eq_zero_iff_ae_notMem]`. Conclude with `hae.mono fun y hy hy' => hy'.2 (hy hy'.1)`. Conclude with `(hopen.measure_ne_zero volume ⟨x, hxI, hx⟩) hnull`. Use `⟨g, hg, closure_minimal hsupp isClosed_Icc, fun ψ hψ => ?_⟩` and prove the remaining obligations.

Establish `hgc : HasCompactSupport g` using `isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) (closure_minimal hsupp isClosed_Icc)`. Establish `hIK : ∀ φ : ℝ → ℂ, Continuous φ → ∀ N, Integrable (fun t => φ t * Kc N t)`. Introduce `φ hφ N`. Take `⟨B, hB⟩` from `(isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hφ.continuousOn`. Use `((hKi N).const_mul B).mono' (hφ.aestronglyMeasurable.mul (hKci N).aestronglyMeasurable) (ae_of_all _ fun t => ?_)` and prove the remaining obligations.

Distinguish the cases in `ht : t ∈ Icc a b`. Rewrite using `[norm_mul]`. Simplify using `only [Kc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK0 N t)]`. Conclude with `mul_le_mul_of_nonneg_right (hB t ht) (hK0 N t)`. Establish `: K N t = 0` using `Function.notMem_support.1 fun h' => ht (hKs N h')`.

Simplify using `[Kc, this]`. Establish `hIg : ∀ φ : ℝ → ℂ, Continuous φ → Integrable (fun t => φ t * g t)` using `fun φ hφ => (hφ.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left`. Use `set L := ∫ t, ‖g t‖ with hLdef`. Establish `hL : 0 ≤ L` using `integral_nonneg fun _ => norm_nonneg _`. Rewrite using `[Metric.tendsto_atTop]`.

Introduce `δ hδ`. Use `set η := δ / (4 * (L + 2)) with hη`. Establish `hηpos : 0 < η` using `by positivity`. Take `⟨ψ', hψ', hψ'c, hψψ'⟩` from `WeakLimit.exists_smooth_near a b hψ hηpos`. Take `⟨N₀, hN₀⟩` from `Metric.tendsto_atTop.1 (hsmooth ψ' hψ' hψ'c) (δ / 2) (by positivity)`.

Use `⟨N₀, fun N hN => ?_⟩` and prove the remaining obligations. Establish `hdiffK : ‖(∫ t, ψ t * Kc N t) - ∫ t, ψ' t * Kc N t‖ ≤ η`. Rewrite using `[← integral_sub (hIK ψ hψ N) (hIK ψ' hψ'.continuous N)]`. Use `(norm_integral_le_of_norm_le ((hKi N).const_mul η) (ae_of_all _ fun t => ?_)).trans ?_` and prove the remaining obligations. Rewrite using `[← sub_mul, norm_mul]`.

Distinguish the cases in `ht : t ∈ Icc a b`. Simplify using `only [Kc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK0 N t)]`. Conclude with `mul_le_mul_of_nonneg_right (hψψ' t ht) (hK0 N t)`. Establish `: K N t = 0` using `Function.notMem_support.1 fun h' => ht (hKs N h')`. Simplify using `[Kc, this]`.

Rewrite using `[integral_const_mul]`. Conclude with `mul_le_of_le_one_right hηpos.le (hK1 N)`. Establish `hdiffg : ‖(∫ t, ψ' t * g t) - ∫ t, ψ t * g t‖ ≤ η * L`. Rewrite using `[← integral_sub (hIg ψ' hψ'.continuous) (hIg ψ hψ), hLdef, ← integral_const_mul]`. Use `norm_integral_le_of_norm_le ((hg.continuous.norm.integrable_of_hasCompactSupport hgc.norm).const_mul η) (ae_of_all _ fun t => ?_)` and prove the remaining obligations.

Rewrite using `[← sub_mul, norm_mul]`. Distinguish the cases in `ht : t ∈ Icc a b`. Rewrite using `[norm_sub_rev]`. Conclude with `mul_le_mul_of_nonneg_right (hψψ' t ht) (norm_nonneg _)`. Establish `: g t = 0` using `Function.notMem_support.1 fun h' => ht (hsupp h')`.

Simplify using `[this]`. Establish `hmid : dist (∫ t, ψ' t * Kc N t) (∫ t, ψ' t * g t) < δ / 2` using `hN₀ N hN`. Rewrite `hmid`, the goal using `[dist_eq_norm]`. Establish `h3 : ‖(∫ t, ψ t * Kc N t) - ∫ t, ψ t * g t‖ ≤ ‖(∫ t, ψ t * Kc N t) - ∫ t, ψ' t * Kc N t‖ + ‖(∫ t, ψ' t * Kc N t) - ∫ t, ψ' t * g t‖ + ‖(∫ t, ψ' t * g t) - ∫ t, ψ t * g t‖` using `(norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (by`. Combine the linear relations using `[norm_sub_le_norm_sub_add_norm_sub (∫ t, ψ' t * Kc N t) (∫ t, ψ' t * g t) (∫ t, ψ t * g t)])`.

Establish `h4 : η + η * L < δ / 2`. Establish `hpos : 0 < 4 * (L + 2)` using `by positivity`. Establish `h5 : η * (4 * (L + 2)) = δ` using `by rw [hη]; field_simp`. Use polynomial arithmetic with `[mul_nonneg hηpos.le hL]`. Use `show ‖(∫ t, ψ t * Kc N t) - ∫ t, ψ t * g t‖ < δ`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_smooth_weak_limit {K : ℕ → ℝ → ℝ} {a b : ℝ} (hKi : ∀ N, Integrable (K N))
    (hK0 : ∀ N t, 0 ≤ K N t) (hK1 : ∀ N, ∫ t, K N t ≤ 1)
    (hKs : ∀ N, Function.support (K N) ⊆ Icc a b)
    (hconv : ∀ ξ : ℝ, ∃ l : ℂ, Tendsto (fun N => 𝓕 (fun t => (K N t : ℂ)) ξ) atTop (𝓝 l))
    (hdecay : ∀ m : ℕ, ∃ C N₀, ∀ N ≥ N₀, ∀ ξ : ℝ,
      ‖𝓕 (fun t => (K N t : ℂ)) ξ‖ ≤ C * (1 + |ξ|) ^ (-(m : ℝ))) :
    ∃ g : ℝ → ℂ, ContDiff ℝ ∞ g ∧ tsupport g ⊆ Icc a b ∧
      ∀ ψ : ℝ → ℂ, Continuous ψ →
        Tendsto (fun N => ∫ t, ψ t * K N t) atTop (𝓝 (∫ t, ψ t * g t)) := by
  set Kc : ℕ → ℝ → ℂ := fun N t => (K N t : ℂ) with hKc
  have hKci : ∀ N, Integrable (Kc N) := fun N => (hKi N).ofReal
  have hKn : ∀ N ξ, ‖𝓕 (Kc N) ξ‖ ≤ 1 := by
    intro N ξ
    refine (WeakLimit.norm_fourier_le _ ξ).trans ?_
    simp only [Kc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK0 N _)]
    exact hK1 N
  choose Φ hΦ using hconv
  have hΦd : ∀ m : ℕ, ∃ C, ∀ ξ, ‖Φ ξ‖ ≤ C * (1 + |ξ|) ^ (-(m : ℝ)) := by
    intro m
    obtain ⟨C, N₀, hC⟩ := hdecay m
    exact ⟨C, fun ξ => le_of_tendsto ((hΦ ξ).norm) (eventually_atTop.2 ⟨N₀, fun N hN => hC N hN ξ⟩)⟩
  have hΦm : AEStronglyMeasurable Φ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun N => (WeakLimit.continuous_fourier_of_integrable (hKci N)).aestronglyMeasurable)
      (ae_of_all _ hΦ)
  have hΦint : ∀ n : ℕ, Integrable (fun ξ : ℝ => ‖ξ‖ ^ n * ‖Φ ξ‖) := by
    intro n
    obtain ⟨C, hC⟩ := hΦd (n + 2)
    have hI : Integrable (fun ξ : ℝ => C * (1 + ‖ξ‖) ^ (-(2 : ℝ))) :=
      (integrable_one_add_norm (by norm_num)).const_mul C
    refine hI.mono' ((continuous_norm.pow n).aestronglyMeasurable.mul hΦm.norm)
      (ae_of_all _ fun ξ => ?_)
    have h1 : 0 < 1 + |ξ| := by positivity
    rw [norm_mul, norm_pow, norm_norm, norm_norm, Real.norm_eq_abs]
    calc |ξ| ^ n * ‖Φ ξ‖ ≤ (1 + |ξ|) ^ n * (C * (1 + |ξ|) ^ (-((n + 2 : ℕ) : ℝ))) :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (by linarith) n) (hC ξ) (norm_nonneg _)
            (by positivity)
      _ = C * (1 + |ξ|) ^ (-(2 : ℝ)) := by
          rw [← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add h1]
          congr 2; push_cast; ring
  have hΦi : Integrable Φ := (integrable_norm_iff hΦm).1 (by simpa using hΦint 0)
  set g : ℝ → ℂ := 𝓕⁻ Φ with hgdef
  have hg : ContDiff ℝ ∞ g := by
    rw [hgdef, Real.fourierInv_eq_fourier_comp_neg]
    exact Real.contDiff_fourier fun n _ => by simpa using (hΦint n).comp_neg

  have hsmooth : ∀ ψ : ℝ → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Tendsto (fun N => ∫ t, ψ t * Kc N t) atTop (𝓝 (∫ t, ψ t * g t)) := by
    intro ψ hψ hψc
    let ψS := hψc.toSchwartzMap hψ
    have hψi : Integrable ψ := hψ.continuous.integrable_of_hasCompactSupport hψc
    have hθi : Integrable (𝓕⁻ ψ) := by
      have := (𝓕⁻ ψS).integrable (μ := volume)
      rwa [SchwartzMap.fourierInv_coe] at this
    have hFψ : Integrable (𝓕 ψ) := by
      have := (𝓕 ψS).integrable (μ := volume)
      rwa [SchwartzMap.fourier_coe] at this
    have hinv : 𝓕 (𝓕⁻ ψ) = ψ := hψ.continuous.fourier_fourierInv_eq hψi hFψ
    have e1 : ∀ N, ∫ t, ψ t * Kc N t = ∫ ξ, 𝓕⁻ ψ ξ * 𝓕 (Kc N) ξ := by
      intro N
      conv_lhs => rw [← hinv]
      exact WeakLimit.integral_fourier_mul_eq hθi (hKci N)
    have e2 : ∫ t, ψ t * g t = ∫ ξ, 𝓕⁻ ψ ξ * Φ ξ :=
      (WeakLimit.integral_fourierInv_mul_eq hψi hΦi).symm
    simp_rw [e1, e2]
    refine tendsto_integral_of_dominated_convergence (fun ξ => ‖𝓕⁻ ψ ξ‖) (fun N => ?_)
      hθi.norm (fun N => ae_of_all _ fun ξ => ?_) (ae_of_all _ fun ξ => (hΦ ξ).const_mul _)
    · exact hθi.aestronglyMeasurable.mul
        (WeakLimit.continuous_fourier_of_integrable (hKci N)).aestronglyMeasurable
    · rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hKn N ξ)

  have hgi : LocallyIntegrable g := hg.continuous.locallyIntegrable
  have hsupp : Function.support g ⊆ Icc a b := by
    have hae : ∀ᵐ x, x ∈ (Icc a b)ᶜ → g x = 0 := by
      refine isClosed_Icc.isOpen_compl.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (hgi.locallyIntegrableOn _) fun φ hφ hφc hφs => ?_
      have hlim := hsmooth (fun x => (φ x : ℂ)) (Complex.ofRealCLM.contDiff.comp hφ)
        (hφc.comp_left Complex.ofReal_zero)
      have h0 : ∀ N, ∫ t, (φ t : ℂ) * Kc N t = 0 := by
        intro N
        refine integral_eq_zero_of_ae (ae_of_all _ fun t => ?_)
        by_cases ht : t ∈ Icc a b
        · have : φ t = 0 := image_eq_zero_of_notMem_tsupport fun h' => hφs h' ht
          simp [this]
        · have : K N t = 0 := Function.notMem_support.1 fun h' => ht (hKs N h')
          simp [Kc, this]
      simp_rw [h0] at hlim
      simp_rw [Complex.real_smul]
      exact tendsto_nhds_unique hlim tendsto_const_nhds
    intro x hx
    by_contra hxI
    have hopen : IsOpen ((Icc a b)ᶜ ∩ Function.support g) :=
      isClosed_Icc.isOpen_compl.inter hg.continuous.isOpen_support
    have hnull : volume ((Icc a b)ᶜ ∩ Function.support g) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      exact hae.mono fun y hy hy' => hy'.2 (hy hy'.1)
    exact (hopen.measure_ne_zero volume ⟨x, hxI, hx⟩) hnull
  refine ⟨g, hg, closure_minimal hsupp isClosed_Icc, fun ψ hψ => ?_⟩
  have hgc : HasCompactSupport g :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) (closure_minimal hsupp isClosed_Icc)
  have hIK : ∀ φ : ℝ → ℂ, Continuous φ → ∀ N, Integrable (fun t => φ t * Kc N t) := by
    intro φ hφ N
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hφ.continuousOn
    refine ((hKi N).const_mul B).mono' (hφ.aestronglyMeasurable.mul (hKci N).aestronglyMeasurable)
      (ae_of_all _ fun t => ?_)
    by_cases ht : t ∈ Icc a b
    · rw [norm_mul]
      simp only [Kc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK0 N t)]
      exact mul_le_mul_of_nonneg_right (hB t ht) (hK0 N t)
    · have : K N t = 0 := Function.notMem_support.1 fun h' => ht (hKs N h')
      simp [Kc, this]
  have hIg : ∀ φ : ℝ → ℂ, Continuous φ → Integrable (fun t => φ t * g t) := fun φ hφ =>
    (hφ.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  set L := ∫ t, ‖g t‖ with hLdef
  have hL : 0 ≤ L := integral_nonneg fun _ => norm_nonneg _
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set η := δ / (4 * (L + 2)) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨ψ', hψ', hψ'c, hψψ'⟩ := WeakLimit.exists_smooth_near a b hψ hηpos
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 (hsmooth ψ' hψ' hψ'c) (δ / 2) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  have hdiffK : ‖(∫ t, ψ t * Kc N t) - ∫ t, ψ' t * Kc N t‖ ≤ η := by
    rw [← integral_sub (hIK ψ hψ N) (hIK ψ' hψ'.continuous N)]
    refine (norm_integral_le_of_norm_le ((hKi N).const_mul η) (ae_of_all _ fun t => ?_)).trans ?_
    · rw [← sub_mul, norm_mul]
      by_cases ht : t ∈ Icc a b
      · simp only [Kc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK0 N t)]
        exact mul_le_mul_of_nonneg_right (hψψ' t ht) (hK0 N t)
      · have : K N t = 0 := Function.notMem_support.1 fun h' => ht (hKs N h')
        simp [Kc, this]
    · rw [integral_const_mul]
      exact mul_le_of_le_one_right hηpos.le (hK1 N)
  have hdiffg : ‖(∫ t, ψ' t * g t) - ∫ t, ψ t * g t‖ ≤ η * L := by
    rw [← integral_sub (hIg ψ' hψ'.continuous) (hIg ψ hψ), hLdef, ← integral_const_mul]
    refine norm_integral_le_of_norm_le ((hg.continuous.norm.integrable_of_hasCompactSupport hgc.norm).const_mul η) (ae_of_all _ fun t => ?_)
    rw [← sub_mul, norm_mul]
    by_cases ht : t ∈ Icc a b
    · rw [norm_sub_rev]
      exact mul_le_mul_of_nonneg_right (hψψ' t ht) (norm_nonneg _)
    · have : g t = 0 := Function.notMem_support.1 fun h' => ht (hsupp h')
      simp [this]
  have hmid : dist (∫ t, ψ' t * Kc N t) (∫ t, ψ' t * g t) < δ / 2 := hN₀ N hN
  rw [dist_eq_norm] at hmid ⊢
  have h3 : ‖(∫ t, ψ t * Kc N t) - ∫ t, ψ t * g t‖ ≤
      ‖(∫ t, ψ t * Kc N t) - ∫ t, ψ' t * Kc N t‖ +
        ‖(∫ t, ψ' t * Kc N t) - ∫ t, ψ' t * g t‖ + ‖(∫ t, ψ' t * g t) - ∫ t, ψ t * g t‖ :=
    (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (by
      linarith [norm_sub_le_norm_sub_add_norm_sub (∫ t, ψ' t * Kc N t) (∫ t, ψ' t * g t)
        (∫ t, ψ t * g t)])
  have h4 : η + η * L < δ / 2 := by
    have hpos : 0 < 4 * (L + 2) := by positivity
    have h5 : η * (4 * (L + 2)) = δ := by rw [hη]; field_simp
    nlinarith [mul_nonneg hηpos.le hL]
  show ‖(∫ t, ψ t * Kc N t) - ∫ t, ψ t * g t‖ < δ
  linarith

end GroundTheory.Automorphic

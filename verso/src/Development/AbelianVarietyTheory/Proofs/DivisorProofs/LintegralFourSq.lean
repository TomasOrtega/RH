import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharacterFourierTransformMemSchwartzBruhatStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.Planch

variable {X : Type} [AddCommGroup X] [TopologicalSpace X]

/- English proof (translation)
Establish `h` using `he.add 0 0 y`. Rewrite `h` using `[add_zero]`. Establish `hn : e 0 y ≠ 0`. Introduce `h0`. Use `he.norm 0 y` as an intermediate fact.

Rewrite `this` using `[h0, norm_zero]`. Conclude with `zero_ne_one this`. Conclude with `mul_left_cancel₀ hn (h.symm.trans (mul_one _).symm)`.
-/
theorem e_zero {e : X → X → ℂ} (he : IsPair e) (y : X) : e 0 y = 1 := by
  have h := he.add 0 0 y
  rw [add_zero] at h
  have hn : e 0 y ≠ 0 := by
    intro h0
    have := he.norm 0 y
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ hn (h.symm.trans (mul_one _).symm)

/- English proof (translation)
Establish `hn : e x y ≠ 0`. Introduce `h0`. Use `he.norm x y` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`. Conclude with `zero_ne_one this`.

Establish `h1 : e (-x) y * e x y = 1` using `by rw [← he.add, neg_add_cancel, e_zero he]`. Establish `h2 : starRingEnd ℂ (e x y) * e x y = 1`. Rewrite using `[Complex.conj_mul', he.norm]`. Simplify using the standard rewrite rules. Conclude with `mul_right_cancel₀ hn (h2.trans h1.symm)`.
-/
theorem conj_e {e : X → X → ℂ} (he : IsPair e) (x y : X) : starRingEnd ℂ (e x y) = e (-x) y := by
  have hn : e x y ≠ 0 := by
    intro h0
    have := he.norm x y
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have h1 : e (-x) y * e x y = 1 := by rw [← he.add, neg_add_cancel, e_zero he]
  have h2 : starRingEnd ℂ (e x y) * e x y = 1 := by
    rw [Complex.conj_mul', he.norm]; simp
  exact mul_right_cancel₀ hn (h2.trans h1.symm)

/- English proof (translation)
Use `haveI := hG.grp`. Use `haveI := hG.t2`. Use `haveI := hG.lc`. Use `haveI := hG.sc`. Use `set Φ := four μ e φ with hΦdef`.

Establish `hΦ : Φ ∈ SB X` using `GlobalTheory.T.bicharacterFourierTransform_mem_schwartzBruhat X hG μ e he φ hφ`. Establish `hec : Continuous (fun p : X × X => e p.1 p.2)` using `he.lc.continuous`. Establish `hint : Integrable (Function.uncurry fun x y => e x y * φ y * starRingEnd ℂ (Φ x)) (μ.prod μ)`. Apply `Continuous.integrable_of_hasCompactSupport` to reduce the goal to its premises. Conclude with `(hec.mul (hφ.1.continuous.comp continuous_snd)).mul ((Complex.continuous_conj.comp hΦ.1.continuous).comp continuous_fst)`.

Apply `HasCompactSupport.intro (hΦ.2.isCompact.prod hφ.2.isCompact)` to reduce the goal to its premises. Introduce and unpack `⟨x, y⟩ hxy`. Simplify using `only [Set.mem_prod, not_and_or] at hxy`. Break down `hxy with h | h` into its components or cases. Simplify using `[image_eq_zero_of_notMem_tsupport h]`.

Simplify using `[image_eq_zero_of_notMem_tsupport h]`. Establish `hinner : ∀ y, ∫ x, e x y * starRingEnd ℂ (Φ x) ∂μ = (C : ℂ) * starRingEnd ℂ (φ y)`. Introduce `y`. Establish `h1 : ∀ x, e x y * starRingEnd ℂ (Φ x) = starRingEnd ℂ (e (-y) x * Φ x)`. Introduce `x`.

Rewrite using `[map_mul, Planch.conj_e he, neg_neg, he.symm]`. Repeatedly rewrite using `[h1]`. Rewrite using `[integral_conj]`. Establish `h2` using `hinv φ hφ (-y)`. Rewrite `h2` using `[neg_neg]`.

Express the relevant statement in the definitionally equal form `starRingEnd ℂ (four μ e Φ (-y)) = _`. Rewrite using `[h2, map_mul, Complex.conj_ofReal]`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use extensionality with `x`.

Rewrite using `[integral_mul_const]`. Both sides reduce to the same expression. Use `_ = ∫ y, ∫ x, e x y * φ y * starRingEnd ℂ (Φ x) ∂μ ∂μ := integral_integral_swap hint`. Use `_ = ∫ y, φ y * ∫ x, e x y * starRingEnd ℂ (Φ x) ∂μ ∂μ := by`. Use `congr 1`.

Use extensionality with `y`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use extensionality with `x`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = (C : ℂ) * ∫ y, φ y * starRingEnd ℂ (φ y) ∂μ := by`. Repeatedly rewrite using `[hinner]`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use extensionality with `y`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_four_mul (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (hG : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ) (he : IsPair e) (C : ℝ) (_hC : 0 < C)
    (hinv : ∀ φ ∈ SB X, ∀ x, four μ e (four μ e φ) x = (C : ℂ) * φ (-x)) (φ : X → ℂ) (hφ : φ ∈ SB X) :
    ∫ x, four μ e φ x * starRingEnd ℂ (four μ e φ x) ∂μ = (C : ℂ) * ∫ y, φ y * starRingEnd ℂ (φ y) ∂μ := by
  haveI := hG.grp; haveI := hG.t2; haveI := hG.lc; haveI := hG.sc
  set Φ := four μ e φ with hΦdef
  have hΦ : Φ ∈ SB X := GlobalTheory.T.bicharacterFourierTransform_mem_schwartzBruhat X hG μ e he φ hφ
  have hec : Continuous (fun p : X × X => e p.1 p.2) := he.lc.continuous
  have hint : Integrable (Function.uncurry fun x y => e x y * φ y * starRingEnd ℂ (Φ x)) (μ.prod μ) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hec.mul (hφ.1.continuous.comp continuous_snd)).mul
        ((Complex.continuous_conj.comp hΦ.1.continuous).comp continuous_fst)
    · apply HasCompactSupport.intro (hΦ.2.isCompact.prod hφ.2.isCompact)
      rintro ⟨x, y⟩ hxy
      simp only [Set.mem_prod, not_and_or] at hxy
      rcases hxy with h | h
      · simp [image_eq_zero_of_notMem_tsupport h]
      · simp [image_eq_zero_of_notMem_tsupport h]
  have hinner : ∀ y, ∫ x, e x y * starRingEnd ℂ (Φ x) ∂μ = (C : ℂ) * starRingEnd ℂ (φ y) := by
    intro y
    have h1 : ∀ x, e x y * starRingEnd ℂ (Φ x) = starRingEnd ℂ (e (-y) x * Φ x) := by
      intro x
      rw [map_mul, Planch.conj_e he, neg_neg, he.symm]
    simp_rw [h1]
    rw [integral_conj]
    have h2 := hinv φ hφ (-y)
    rw [neg_neg] at h2
    change starRingEnd ℂ (four μ e Φ (-y)) = _
    rw [h2, map_mul, Complex.conj_ofReal]
  calc ∫ x, Φ x * starRingEnd ℂ (Φ x) ∂μ
      = ∫ x, ∫ y, e x y * φ y * starRingEnd ℂ (Φ x) ∂μ ∂μ := by
        congr 1; ext x
        rw [integral_mul_const]
        rfl
    _ = ∫ y, ∫ x, e x y * φ y * starRingEnd ℂ (Φ x) ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ y, φ y * ∫ x, e x y * starRingEnd ℂ (Φ x) ∂μ ∂μ := by
        congr 1; ext y
        rw [← integral_const_mul]
        congr 1; ext x; ring
    _ = (C : ℂ) * ∫ y, φ y * starRingEnd ℂ (φ y) ∂μ := by
        simp_rw [hinner]
        rw [← integral_const_mul]
        congr 1; ext y; ring

/- English proof (translation)
Introduce `X _ _ _ _ hG μ _ e he C hC hinv φ hφ`. Use `haveI := hG.grp`. Use `haveI := hG.t2`. Use `haveI := hG.lc`. Use `haveI := hG.sc`.

Establish `hΦ : four μ e φ ∈ SB X` using `GlobalTheory.T.bicharacterFourierTransform_mem_schwartzBruhat X hG μ e he φ hφ`. Establish `hL : ∀ f ∈ SB X, ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂μ)`. Introduce `f hf`. Establish `h1 : Continuous f` using `hf.1.continuous`. Establish `h2 : HasCompactSupport f` using `hf.2`.

Establish `h3 : HasCompactSupport (fun x => ‖f x‖ ^ 2)`. Use `h2.norm` as an intermediate fact. Conclude with `this.mul_right (f' := fun x => ‖f x‖) |>.mono (fun x hx => by simpa [sq] using hx)`. Establish `hi : Integrable (fun x => ‖f x‖ ^ 2) μ` using `(h1.norm.pow 2).integrable_of_hasCompactSupport h3`. Rewrite using `[ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => by positivity)]`.

Use `congr 1`. Use extensionality with `x`. Rewrite using `[← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]`. Establish `hC' : ∀ f : X → ℂ, ∫ x, f x * starRingEnd ℂ (f x) ∂μ = ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ)`. Introduce `f`.

Rewrite using `[← integral_complex_ofReal]`. Use `congr 1`. Use extensionality with `x`. Rewrite using `[Complex.mul_conj']`. Use `push_cast`.

Both sides reduce to the same expression. Establish `hk` using `integral_four_mul X hG μ e he C hC hinv φ hφ`. Rewrite `hk` using `[hC', hC']`. Establish `hk' : ∫ x, ‖four μ e φ x‖ ^ 2 ∂μ = C * ∫ x, ‖φ x‖ ^ 2 ∂μ` using `by exact_mod_cast hk`. Rewrite using `[hL _ hΦ, hL _ hφ, hk', ENNReal.ofReal_mul hC.le]`.
-/
theorem lintegral_four_sq : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∀ C : ℝ, 0 < C → (∀ φ ∈ SB X, ∀ x, four μ e (four μ e φ) x = (C : ℂ) * φ (-x)) → ∀ φ ∈ SB X, ∫⁻ x, ‖four μ e φ x‖ₑ ^ 2 ∂μ = ENNReal.ofReal C * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  intro X _ _ _ _ hG μ _ e he C hC hinv φ hφ
  haveI := hG.grp; haveI := hG.t2; haveI := hG.lc; haveI := hG.sc
  have hΦ : four μ e φ ∈ SB X := GlobalTheory.T.bicharacterFourierTransform_mem_schwartzBruhat X hG μ e he φ hφ
  have hL : ∀ f ∈ SB X, ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂μ) := by
    intro f hf
    have h1 : Continuous f := hf.1.continuous
    have h2 : HasCompactSupport f := hf.2
    have h3 : HasCompactSupport (fun x => ‖f x‖ ^ 2) := by
      have := h2.norm
      exact this.mul_right (f' := fun x => ‖f x‖) |>.mono (fun x hx => by simpa [sq] using hx)
    have hi : Integrable (fun x => ‖f x‖ ^ 2) μ :=
      (h1.norm.pow 2).integrable_of_hasCompactSupport h3
    rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => by positivity)]
    congr 1; ext x
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  have hC' : ∀ f : X → ℂ, ∫ x, f x * starRingEnd ℂ (f x) ∂μ = ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    intro f
    rw [← integral_complex_ofReal]
    congr 1; ext x
    rw [Complex.mul_conj']
    push_cast; rfl
  have hk := integral_four_mul X hG μ e he C hC hinv φ hφ
  rw [hC', hC'] at hk
  have hk' : ∫ x, ‖four μ e φ x‖ ^ 2 ∂μ = C * ∫ x, ‖φ x‖ ^ 2 ∂μ := by exact_mod_cast hk
  rw [hL _ hΦ, hL _ hφ, hk', ENNReal.ofReal_mul hC.le]

end GlobalTheory.KSp.Planch

end

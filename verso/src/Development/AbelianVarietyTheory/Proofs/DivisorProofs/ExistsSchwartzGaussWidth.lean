import Mathlib
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
open FourierTransform MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.GaussWidths

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- English proof (translation)
Use `set t : ℝ := Real.sqrt (c / Real.pi) with ht_def`. Establish `ht : t ≠ 0` using `(Real.sqrt_pos.2 (div_pos hc Real.pi_pos)).ne'`. Establish `ht2 : t ^ 2 = c / Real.pi` using `Real.sq_sqrt (div_pos hc Real.pi_pos).le`. Set `e : E ≃L[ℝ] E` to `(LinearEquiv.smulOfNeZero ℝ E t ht).toContinuousLinearEquiv`. Use `⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (GroundTheory.Global.gaussianSchwartz E), fun y => ?_⟩` and prove the remaining obligations.

Rewrite using `[SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, GroundTheory.Global.gaussianSchwartz_apply, Complex.ofReal_exp]`. Use `congr 1`. Establish `hey : e y = t • y` using `rfl`. Rewrite using `[hey, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ht2]`. Establish `hpi : Real.pi ≠ 0` using `Real.pi_ne_zero`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_schwartz_gauss_width (c : ℝ) (hc : 0 < c) :
    ∃ g : SchwartzMap E ℂ, ∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) := by
  set t : ℝ := Real.sqrt (c / Real.pi) with ht_def
  have ht : t ≠ 0 := (Real.sqrt_pos.2 (div_pos hc Real.pi_pos)).ne'
  have ht2 : t ^ 2 = c / Real.pi := Real.sq_sqrt (div_pos hc Real.pi_pos).le
  let e : E ≃L[ℝ] E := (LinearEquiv.smulOfNeZero ℝ E t ht).toContinuousLinearEquiv
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (GroundTheory.Global.gaussianSchwartz E), fun y => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply, Complex.ofReal_exp]
  congr 1
  have hey : e y = t • y := rfl
  rw [hey, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ht2]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp

/- English proof (translation)
Introduce `g hg`. Establish `: g = K⁻¹ • u`. Use extensionality with `y`. Rewrite using `[SchwartzMap.smul_apply, hu, hg, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hK, one_mul]`. Rewrite using `[this]`.

Conclude with `M.smul_mem _ huM`.
-/
theorem mem_of_smul {M : Submodule ℂ (SchwartzMap E ℂ)} (c : ℝ) (K : ℂ) (hK : K ≠ 0)
    (u : SchwartzMap E ℂ) (hu : ∀ y, u y = K * Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)))
    (huM : u ∈ M) :
    ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M := by
  intro g hg
  have : g = K⁻¹ • u := by
    ext y
    rw [SchwartzMap.smul_apply, hu, hg, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hK, one_mul]
  rw [this]
  exact M.smul_mem _ huM

variable [MeasurableSpace E] [BorelSpace E]

/- English proof (translation)
Establish `hsc : 0 < s + c` using `by linarith`. Establish `key : ∀ a : E, Complex.exp (-((s * ‖a‖ ^ 2 : ℝ) : ℂ)) * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) = Complex.exp (-((s + c : ℝ) : ℂ) * (‖a‖ : ℂ) ^ 2 + ((2 * c : ℝ) : ℂ) * ((inner ℝ y a : ℝ) : ℂ)) * Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))`. Introduce `a`. Rewrite using `[← Complex.exp_add, ← Complex.exp_add]`. Use `congr 1`.

Rewrite using `[norm_sub_sq_real]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[key]`. Rewrite using `[integral_mul_const, GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by simpa using hsc) _ y, mul_assoc, ← Complex.exp_add]`.

Use `congr 2`. Establish `h1 : ((s + c : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hsc.ne'`. Move the coercions through the operations in `at h1 ⊢`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_gauss_mul_gauss (s c : ℝ) (hs : 0 < s) (hc : 0 < c) (y : E) :
    ∫ a : E, Complex.exp (-((s * ‖a‖ ^ 2 : ℝ) : ℂ)) * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) =
      ((Real.pi : ℂ) / ((s + c : ℝ) : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) *
        Complex.exp (-(((s * c / (s + c)) * ‖y‖ ^ 2 : ℝ) : ℂ)) := by
  have hsc : 0 < s + c := by linarith
  have key : ∀ a : E, Complex.exp (-((s * ‖a‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) =
      Complex.exp (-((s + c : ℝ) : ℂ) * (‖a‖ : ℂ) ^ 2 + ((2 * c : ℝ) : ℂ) * ((inner ℝ y a : ℝ) : ℂ)) *
        Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) := by
    intro a
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [norm_sub_sq_real]
    push_cast
    ring
  simp_rw [key]
  rw [integral_mul_const, GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (by simpa using hsc) _ y, mul_assoc, ← Complex.exp_add]
  congr 2
  have h1 : ((s + c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsc.ne'
  push_cast at h1 ⊢
  field_simp
  ring

end GlobalTheory.GaussWidths

namespace GlobalTheory.GaussWidths

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def HasWidth (M : Submodule ℂ (SchwartzMap E ℂ)) (c : ℝ) : Prop :=
  ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M

def ConvStable (M : Submodule ℂ (SchwartzMap E ℂ)) : Prop :=
  ∀ (b c : ℝ), 0 < b → 0 < c →
    (∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M) →
    ∀ (h u : SchwartzMap E ℂ),
      (∀ y, u y = ∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a *
        Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) → u ∈ M

/- English proof (translation)
Introduce `h`. Rewrite `h` using `[Complex.cpow_eq_zero_iff]`. Conclude with `(Complex.ofReal_ne_zero.2 hr.ne') h.1`.
-/
theorem cpow_ne_zero_of_pos (r : ℝ) (hr : 0 < r) (z : ℂ) : ((r : ℂ)) ^ z ≠ 0 := by
  intro h
  rw [Complex.cpow_eq_zero_iff] at h
  exact (Complex.ofReal_ne_zero.2 hr.ne') h.1

/- English proof (translation)
Use `set s : ℝ := c * c' / (c - c') with hs_def`. Establish `hcc : 0 < c - c'` using `by linarith`. Establish `hs : 0 < s` using `div_pos (mul_pos hc hc') hcc`. Establish `hsc : s * c / (s + c) = c'`. Rewrite using `[hs_def]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Take `⟨h, hh⟩` from `exists_schwartz_gauss_width (E := E) (s / 2) (by linarith)`. Take `⟨g', hg'⟩` from `exists_schwartz_gauss_width (E := E) c' hc'`. Use `set K : ℂ := ((Real.pi : ℂ) / ((s + c : ℝ) : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ)`.

Establish `hK : K ≠ 0`. Establish `: (Real.pi : ℂ) / ((s + c : ℝ) : ℂ) = ((Real.pi / (s + c) : ℝ) : ℂ)` using `by push_cast; rfl`. Simplify using `only [K, this]`. Conclude with `cpow_ne_zero_of_pos _ (div_pos Real.pi_pos (by linarith)) _`. Establish `huM : K • g' ∈ M` using `hconv (s / 2) c (by linarith) hc hP h (K • g') (fun y => by`.

Rewrite using `[SchwartzMap.smul_apply, smul_eq_mul, hg', ← hsc, ← integral_gauss_mul_gauss s c hs hc y]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Rewrite using `[hh]`. Simplify using `only [← Complex.exp_add]`.

Use `congr 1`. Use `push_cast`. Use the proof step `ring)`. Conclude with `mem_of_smul c' K hK (K • g') (fun y => by rw [SchwartzMap.smul_apply, smul_eq_mul, hg']) huM`.
-/
theorem hasWidth_of_lt {M : Submodule ℂ (SchwartzMap E ℂ)} (hconv : ConvStable M) (c : ℝ)
    (hc : 0 < c) (hP : HasWidth M c) (c' : ℝ) (hc' : 0 < c') (hlt : c' < c) : HasWidth M c' := by
  set s : ℝ := c * c' / (c - c') with hs_def
  have hcc : 0 < c - c' := by linarith
  have hs : 0 < s := div_pos (mul_pos hc hc') hcc
  have hsc : s * c / (s + c) = c' := by
    rw [hs_def]; field_simp; ring
  obtain ⟨h, hh⟩ := exists_schwartz_gauss_width (E := E) (s / 2) (by linarith)
  obtain ⟨g', hg'⟩ := exists_schwartz_gauss_width (E := E) c' hc'
  set K : ℂ := ((Real.pi : ℂ) / ((s + c : ℝ) : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ)
  have hK : K ≠ 0 := by
    have : (Real.pi : ℂ) / ((s + c : ℝ) : ℂ) = ((Real.pi / (s + c) : ℝ) : ℂ) := by push_cast; rfl
    simp only [K, this]
    exact cpow_ne_zero_of_pos _ (div_pos Real.pi_pos (by linarith)) _
  have huM : K • g' ∈ M := hconv (s / 2) c (by linarith) hc hP h (K • g') (fun y => by
    rw [SchwartzMap.smul_apply, smul_eq_mul, hg', ← hsc, ← integral_gauss_mul_gauss s c hs hc y]
    congr 1
    funext a
    rw [hh]
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring)
  exact mem_of_smul c' K hK (K • g') (fun y => by rw [SchwartzMap.smul_apply, smul_eq_mul, hg']) huM

/- English proof (translation)
Take `⟨g, hg⟩` from `exists_schwartz_gauss_width (E := E) c hc`. Use `set K : ℂ := ((Real.pi : ℂ) / (c : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ)`. Establish `hK : K ≠ 0`. Establish `: (Real.pi : ℂ) / (c : ℂ) = ((Real.pi / c : ℝ) : ℂ)` using `by push_cast; rfl`. Simplify using `only [K, this]`.

Conclude with `cpow_ne_zero_of_pos _ (div_pos Real.pi_pos hc) _`. Use `mem_of_smul (Real.pi ^ 2 / c) K hK (𝓕 g) (fun w => ?_) (hF g (hP g hg))` and prove the remaining obligations. Establish `hfun : (g : E → ℂ) = fun v => Complex.exp (-(c : ℂ) * (‖v‖ : ℂ) ^ 2)`. Use function extensionality and compare the values at `v`. Rewrite using `[hg]`.

Use `push_cast`. Put the polynomial expressions in normal form. Rewrite using `[SchwartzMap.fourier_coe, hfun, fourier_gaussian_innerProductSpace (by simpa using hc)]`. Use `congr 2`. Establish `: (c : ℂ) ≠ 0` using `by exact_mod_cast hc.ne'`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem hasWidth_fourier {M : Submodule ℂ (SchwartzMap E ℂ)} (hF : ∀ f ∈ M, 𝓕 f ∈ M) (c : ℝ)
    (hc : 0 < c) (hP : HasWidth M c) : HasWidth M (Real.pi ^ 2 / c) := by
  obtain ⟨g, hg⟩ := exists_schwartz_gauss_width (E := E) c hc
  set K : ℂ := ((Real.pi : ℂ) / (c : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ)
  have hK : K ≠ 0 := by
    have : (Real.pi : ℂ) / (c : ℂ) = ((Real.pi / c : ℝ) : ℂ) := by push_cast; rfl
    simp only [K, this]
    exact cpow_ne_zero_of_pos _ (div_pos Real.pi_pos hc) _
  refine mem_of_smul (Real.pi ^ 2 / c) K hK (𝓕 g) (fun w => ?_) (hF g (hP g hg))
  have hfun : (g : E → ℂ) = fun v => Complex.exp (-(c : ℂ) * (‖v‖ : ℂ) ^ 2) := by
    funext v; rw [hg]; push_cast; ring_nf
  rw [SchwartzMap.fourier_coe, hfun, fourier_gaussian_innerProductSpace (by simpa using hc)]
  congr 2
  have : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  push_cast
  field_simp

/- English proof (translation)
Break down `lt_trichotomy c Real.pi with hlt | heq | hgt` into its components or cases. Conclude with `hasWidth_of_lt hconv Real.pi Real.pi_pos hπ c hc hlt`. Conclude with `heq ▸ hπ`. Establish `hc' : 0 < Real.pi ^ 2 / c` using `by positivity`. Establish `hlt : Real.pi ^ 2 / c < Real.pi`.

Rewrite using `[div_lt_iff₀ hc]`. Use polynomial arithmetic with `[Real.pi_pos]`. Establish `h1` using `hasWidth_fourier hF _ hc' (hasWidth_of_lt hconv Real.pi Real.pi_pos hπ _ hc' hlt)`. Establish `: Real.pi ^ 2 / (Real.pi ^ 2 / c) = c`. Use `Real.pi_pos.ne'` as an intermediate fact.

Clear the denominators using the available nonvanishing facts. Rewrite `h1` using `[this]`. Then use the resulting hypothesis.
-/
theorem hasWidth_all {M : Submodule ℂ (SchwartzMap E ℂ)} (hconv : ConvStable M)
    (hF : ∀ f ∈ M, 𝓕 f ∈ M) (hπ : HasWidth M Real.pi) (c : ℝ) (hc : 0 < c) : HasWidth M c := by
  rcases lt_trichotomy c Real.pi with hlt | heq | hgt
  · exact hasWidth_of_lt hconv Real.pi Real.pi_pos hπ c hc hlt
  · exact heq ▸ hπ
  · have hc' : 0 < Real.pi ^ 2 / c := by positivity
    have hlt : Real.pi ^ 2 / c < Real.pi := by
      rw [div_lt_iff₀ hc]; nlinarith [Real.pi_pos]
    have h1 := hasWidth_fourier hF _ hc' (hasWidth_of_lt hconv Real.pi Real.pi_pos hπ _ hc' hlt)
    have : Real.pi ^ 2 / (Real.pi ^ 2 / c) = c := by
      have := Real.pi_pos.ne'; field_simp
    rwa [this] at h1

/- English proof (translation)
Introduce `g hg`. Establish `: g = G` using `by ext y; rw [hg, hG]`. Rewrite using `[this]` and apply the resulting hypothesis.
-/
theorem hasWidth_pi {M : Submodule ℂ (SchwartzMap E ℂ)} (G : SchwartzMap E ℂ)
    (hG : ∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) (hGM : G ∈ M) :
    HasWidth M Real.pi := by
  intro g hg
  have : g = G := by ext y; rw [hg, hG]
  rwa [this]

end GlobalTheory.GaussWidths

namespace GlobalTheory.GaussWidths

/- English proof (translation)
Introduce `E _ _ _ _ _ M hM hℓ hF G hG hGM c hc g hg`. Conclude with `hasWidth_all (fun b c' hb hc' hP h u hu => hconvAll E M hM hℓ b c' hb hc' hP h u hu) hF (hasWidth_pi G hG hGM) c hc g hg`.
-/
theorem all_widths_of_conv
    (hconvAll : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E]
      (M : Submodule ℂ (SchwartzMap E ℂ)), IsClosed (M : Set (SchwartzMap E ℂ)) →
      (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
      ∀ (b c : ℝ), 0 < b → 0 < c →
      (∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M) →
      ∀ (h u : SchwartzMap E ℂ),
        (∀ y, u y = ∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a *
          Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) →
        u ∈ M) :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Submodule ℂ (SchwartzMap E ℂ)), IsClosed (M : Set (SchwartzMap E ℂ)) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
    (∀ f ∈ M, 𝓕 f ∈ M) →
    ∀ G : SchwartzMap E ℂ, (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ M →
    ∀ (c : ℝ), 0 < c → ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M := by
  intro E _ _ _ _ _ M hM hℓ hF G hG hGM c hc g hg
  exact hasWidth_all (fun b c' hb hc' hP h u hu => hconvAll E M hM hℓ b c' hb hc' hP h u hu) hF
    (hasWidth_pi G hG hGM) c hc g hg

end GlobalTheory.GaussWidths

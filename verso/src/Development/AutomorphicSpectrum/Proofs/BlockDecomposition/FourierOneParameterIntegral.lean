import Mathlib
open MeasureTheory

namespace GlobalTheory.CompanionTheory.OneParamFourier

variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [MeasurableSpace A] [BorelSpace A]

/- English proof (translation)
Establish `h` using `integral_add_right_eq_self (μ := lam) (fun b => H b * χ (b + -a)) a`. Simplify using `only [add_neg_cancel_right] at h`. Rewrite using `[h, ← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)` and prove the remaining obligations. Simplify using `only [AddChar.map_add_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_translate_mul_char (lam : Measure A) [lam.IsAddHaarMeasure] (H : A → ℂ)
    (χ : AddChar A ℂ) (a : A) :
    ∫ b, H (b + a) * χ b ∂lam = χ (-a) * ∫ b, H b * χ b ∂lam := by
  have h := integral_add_right_eq_self (μ := lam) (fun b => H b * χ (b + -a)) a
  simp only [add_neg_cancel_right] at h
  rw [h, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only [AddChar.map_add_eq_mul]
  ring

/- English proof (translation)
Use `hH.mono (hH.aestronglyMeasurable.mul hχ.aestronglyMeasurable) (Filter.Eventually.of_forall fun b => ?_)` and prove the remaining obligations. Simplify using `[hn]`.
-/
theorem integrable_mul_char {lam : Measure A} {H : A → ℂ} (hH : Integrable H lam)
    {χ : AddChar A ℂ} (hχ : Continuous χ) (hn : ∀ x, ‖χ x‖ = 1) :
    Integrable (fun b => H b * χ b) lam := by
  refine hH.mono (hH.aestronglyMeasurable.mul hχ.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun b => ?_)
  simp [hn]

/- English proof (translation)
Establish `hcont : Continuous (Function.uncurry fun (u : ℝ) (b : A) => K * G (b + c u) * χ b)`. Unfold `Function.uncurry`. Use `fun_prop`. Use `haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) s)) := by`. Unfold `Set.uIoc`.

Use `infer_instance`. Use `(integrable_prod_iff hcont.aestronglyMeasurable).2 ⟨ae_of_all _ fun u => ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : Integrable (fun b => G (b + c u)) lam` using `hGi.comp_add_right (c u)`. Establish `h2` using `integrable_mul_char (h1.const_mul K) hχ hn`. Simplify `h2` using `[Function.uncurry, mul_assoc]`.

Establish `hconst : ∀ u : ℝ, ∫ b, ‖Function.uncurry (fun (u : ℝ) (b : A) => K * G (b + c u) * χ b) (u, b)‖ ∂lam = ‖K‖ * ∫ b, ‖G b‖ ∂lam`. Introduce `u`. Establish `h` using `integral_add_right_eq_self (μ := lam) (fun b => ‖G b‖) (c u)`. Rewrite using `[← h, ← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)` and prove the remaining obligations.

Simplify using `[Function.uncurry, hn]`. Repeatedly rewrite using `[hconst]`. Conclude with `integrable_const _`.
-/
theorem integrable_uncurry_translate (lam : Measure A) [lam.IsAddHaarMeasure] [SFinite lam]
    (c : ℝ →+ A) (hc : Continuous c) {G : A → ℂ} (hG : Continuous G) (hGi : Integrable G lam)
    {χ : AddChar A ℂ} (hχ : Continuous χ) (hn : ∀ x, ‖χ x‖ = 1) (K : ℂ) (s : ℝ) :
    Integrable (Function.uncurry fun (u : ℝ) (b : A) => K * G (b + c u) * χ b)
      ((volume.restrict (Set.uIoc 0 s)).prod lam) := by
  have hcont : Continuous (Function.uncurry fun (u : ℝ) (b : A) => K * G (b + c u) * χ b) := by
    unfold Function.uncurry
    fun_prop
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) s)) := by
    unfold Set.uIoc
    infer_instance
  refine (integrable_prod_iff hcont.aestronglyMeasurable).2 ⟨ae_of_all _ fun u => ?_, ?_⟩
  · have h1 : Integrable (fun b => G (b + c u)) lam := hGi.comp_add_right (c u)
    have h2 := integrable_mul_char (h1.const_mul K) hχ hn
    simpa [Function.uncurry, mul_assoc] using h2
  · have hconst : ∀ u : ℝ, ∫ b, ‖Function.uncurry (fun (u : ℝ) (b : A) => K * G (b + c u) * χ b) (u, b)‖ ∂lam
        = ‖K‖ * ∫ b, ‖G b‖ ∂lam := by
      intro u
      have h := integral_add_right_eq_self (μ := lam) (fun b => ‖G b‖) (c u)
      rw [← h, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp [Function.uncurry, hn]
    simp_rw [hconst]
    exact integrable_const _

/- English proof (translation)
Use `set K : ℂ := 2 * Real.pi * Complex.I with hK`. Establish `hK0 : K ≠ 0`. Simplify using `[hK, Real.pi_ne_zero, Complex.I_ne_zero]`. Use `set e : ℝ → ℂ := fun u => Complex.exp (K * ((u * f : ℝ) : ℂ)) with he`. Establish `hχe : ∀ s : ℝ, χ (-(c s)) = e s`.

Introduce `s`. Rewrite using `[← map_neg, hf, he]`. Simplify using `only`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `set Fh : ℂ := ∫ b, F b * χ b ∂lam with hFh`. Use `set Gh : ℂ := ∫ b, G b * χ b ∂lam with hGh`. Establish `hec : Continuous e`. Rewrite using `[he]`.

Use `fun_prop`. Establish `key : ∀ s : ℝ, (e s - 1) * Fh = K * Gh * ∫ u in (0 : ℝ)..s, e u`. Introduce `s`. Establish `hftc : ∀ b : A, F (b + c s) - F b = ∫ u in (0 : ℝ)..s, K * G (b + c u)`. Introduce `b`.

Establish `hcu : Continuous fun u : ℝ => K * G (b + c u)` using `by fun_prop`. Use `intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := s) (f := fun t : ℝ => F (b + c t)) (f' := fun u => K * G (b + c u)) (fun x _ => hd b x) (hcu.intervalIntegrable _ _)` as an intermediate fact. Simplify using `using this.symm`. Establish `hswap` using `intervalIntegral_integral_swap (integrable_uncurry_translate lam c hc hG hGi hχ hn K s)`. Establish `h1 : ∫ b, F (b + c s) * χ b ∂lam = e s * Fh`.

Rewrite using `[integral_translate_mul_char, hχe]`. Establish `hi1 : Integrable (fun b => F (b + c s) * χ b) lam` using `integrable_mul_char (hFi.comp_add_right (c s)) hχ hn`. Establish `hi2 : Integrable (fun b => F b * χ b) lam` using `integrable_mul_char hFi hχ hn`. Establish `h2 : (e s - 1) * Fh = ∫ b, (∫ u in (0 : ℝ)..s, K * G (b + c u) * χ b) ∂lam`. Establish `: (e s - 1) * Fh = ∫ b, (F (b + c s) * χ b - F b * χ b) ∂lam`.

Rewrite using `[integral_sub hi1 hi2, h1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[intervalIntegral.integral_mul_const, ← hftc b]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2, ← hswap, ← intervalIntegral.integral_const_mul]`. Use `intervalIntegral.integral_congr fun u _ => ?_` and prove the remaining obligations. Use `beta_reduce`.

Establish `h3 : ∫ b, K * G (b + c u) * χ b ∂lam = K * ∫ b, G (b + c u) * χ b ∂lam`. Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)` and prove the remaining obligations. Simplify using `only`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h3, integral_translate_mul_char, hχe]`. Expand and normalize the polynomial expressions, which then agree. Establish `hL : HasDerivAt (fun s : ℝ => (e s - 1) * Fh) (K * f * Fh) 0`. Establish `h0 : HasDerivAt (fun u : ℝ => K * ((u * f : ℝ) : ℂ)) (K * f) 0`. Establish `: HasDerivAt (fun u : ℝ => ((u : ℂ))) 1 0` using `Complex.ofRealCLM.hasDerivAt`.

Simplify `(this.mul_const (f : ℂ)).const_mul K` using `[mul_assoc]`. Use `((h0.cexp).sub_const 1).mul_const Fh` as an intermediate fact. Simplify `this` using `[he]`. Establish `hR : HasDerivAt (fun s : ℝ => K * Gh * ∫ u in (0 : ℝ)..s, e u) (K * Gh) 0`. Use `(hec.integral_hasStrictDerivAt 0 0).hasDerivAt.const_mul (K * Gh)` as an intermediate fact.

Simplify `this` using `[he]`. Establish `hEq : (fun s : ℝ => (e s - 1) * Fh) = fun s : ℝ => K * Gh * ∫ u in (0 : ℝ)..s, e u`. Use function extensionality and compare the values at `key`. Rewrite `hL` using `[hEq]`. Use `hL.unique hR` as an intermediate fact.

Establish `h4 : K * (f * Fh) = K * Gh`. Rewrite using `[← mul_assoc]`. Conclude with `this`. Conclude with `(mul_left_cancel₀ hK0 h4).symm`.
-/
theorem integral_mul_char_eq_of_hasDerivAt (A : Type) [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A] (lam : Measure A)
    [lam.IsAddHaarMeasure] [SFinite lam] (c : ℝ →+ A) (hc : Continuous c) (F G : A → ℂ)
    (hF : Continuous F) (hG : Continuous G) (hFi : Integrable F lam) (hGi : Integrable G lam)
    (χ : AddChar A ℂ) (hχ : Continuous χ) (hn : ∀ x, ‖χ x‖ = 1) (f : ℝ)
    (hf : ∀ s : ℝ, χ (c s) = Complex.exp (-(2 * Real.pi * Complex.I * ((s * f : ℝ) : ℂ))))
    (hd : ∀ (b : A) (s : ℝ),
      HasDerivAt (fun t : ℝ => F (b + c t)) (2 * Real.pi * Complex.I * G (b + c s)) s) :
    ∫ b, G b * χ b ∂lam = (f : ℂ) * ∫ b, F b * χ b ∂lam := by
  set K : ℂ := 2 * Real.pi * Complex.I with hK
  have hK0 : K ≠ 0 := by
    simp [hK, Real.pi_ne_zero, Complex.I_ne_zero]
  set e : ℝ → ℂ := fun u => Complex.exp (K * ((u * f : ℝ) : ℂ)) with he
  have hχe : ∀ s : ℝ, χ (-(c s)) = e s := by
    intro s
    rw [← map_neg, hf, he]
    simp only
    congr 1
    push_cast
    ring
  set Fh : ℂ := ∫ b, F b * χ b ∂lam with hFh
  set Gh : ℂ := ∫ b, G b * χ b ∂lam with hGh
  have hec : Continuous e := by
    rw [he]
    fun_prop
  have key : ∀ s : ℝ, (e s - 1) * Fh = K * Gh * ∫ u in (0 : ℝ)..s, e u := by
    intro s
    have hftc : ∀ b : A, F (b + c s) - F b = ∫ u in (0 : ℝ)..s, K * G (b + c u) := by
      intro b
      have hcu : Continuous fun u : ℝ => K * G (b + c u) := by fun_prop
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := s)
        (f := fun t : ℝ => F (b + c t)) (f' := fun u => K * G (b + c u))
        (fun x _ => hd b x) (hcu.intervalIntegrable _ _)
      simpa using this.symm
    have hswap := intervalIntegral_integral_swap
      (integrable_uncurry_translate lam c hc hG hGi hχ hn K s)
    have h1 : ∫ b, F (b + c s) * χ b ∂lam = e s * Fh := by
      rw [integral_translate_mul_char, hχe]
    have hi1 : Integrable (fun b => F (b + c s) * χ b) lam :=
      integrable_mul_char (hFi.comp_add_right (c s)) hχ hn
    have hi2 : Integrable (fun b => F b * χ b) lam := integrable_mul_char hFi hχ hn
    have h2 : (e s - 1) * Fh = ∫ b, (∫ u in (0 : ℝ)..s, K * G (b + c u) * χ b) ∂lam := by
      have : (e s - 1) * Fh = ∫ b, (F (b + c s) * χ b - F b * χ b) ∂lam := by
        rw [integral_sub hi1 hi2, h1]
        ring
      rw [this]
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp only
      rw [intervalIntegral.integral_mul_const, ← hftc b]
      ring
    rw [h2, ← hswap, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    beta_reduce
    have h3 : ∫ b, K * G (b + c u) * χ b ∂lam = K * ∫ b, G (b + c u) * χ b ∂lam := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp only
      ring
    rw [h3, integral_translate_mul_char, hχe]
    ring
  have hL : HasDerivAt (fun s : ℝ => (e s - 1) * Fh) (K * f * Fh) 0 := by
    have h0 : HasDerivAt (fun u : ℝ => K * ((u * f : ℝ) : ℂ)) (K * f) 0 := by
      have : HasDerivAt (fun u : ℝ => ((u : ℂ))) 1 0 := Complex.ofRealCLM.hasDerivAt
      simpa [mul_assoc] using (this.mul_const (f : ℂ)).const_mul K
    have := ((h0.cexp).sub_const 1).mul_const Fh
    simpa [he] using this
  have hR : HasDerivAt (fun s : ℝ => K * Gh * ∫ u in (0 : ℝ)..s, e u) (K * Gh) 0 := by
    have := (hec.integral_hasStrictDerivAt 0 0).hasDerivAt.const_mul (K * Gh)
    simpa [he] using this
  have hEq : (fun s : ℝ => (e s - 1) * Fh) = fun s : ℝ => K * Gh * ∫ u in (0 : ℝ)..s, e u :=
    funext key
  rw [hEq] at hL
  have := hL.unique hR
  have h4 : K * (f * Fh) = K * Gh := by
    rw [← mul_assoc]
    exact this
  exact (mul_left_cancel₀ hK0 h4).symm

end GlobalTheory.CompanionTheory.OneParamFourier

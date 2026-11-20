import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `ψ hψ`. Set `E : ℂ → ℂˣ` to `fun w => Units.mk0 (Complex.exp w) (Complex.exp_ne_zero w)`. Establish `hE : Continuous E`. Use `Units.continuous_iff.2 ⟨Complex.continuous_exp, ?_⟩` and prove the remaining obligations. Establish `: (fun w => ((E w)⁻¹ : ℂˣ).val) = fun w => (Complex.exp w)⁻¹`.

Use function extensionality and compare the values at `w`. Simplify using `[E]`. Rewrite using `[this]`. Conclude with `Complex.continuous_exp.inv₀ Complex.exp_ne_zero`. Establish `hEadd : ∀ x y, E (x + y) = E x * E y` using `fun x y => Units.ext (Complex.exp_add x y)`.

Establish `hE0 : E 0 = 1` using `Units.ext Complex.exp_zero`. Set `f : C(ℂ, {z : ℂ // z ≠ 0})` to `⟨fun w => ⟨(ψ (E w) : ℂ), Units.ne_zero _⟩, (Units.continuous_val.comp (hψ.comp hE)).subtype_mk _⟩`. Take `⟨F, ⟨hF0, hF⟩, -⟩` from `Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0 (Subtype.ext (by simp [f, hE0]))`. Establish `hF' : ∀ w, Complex.exp (F w) = (ψ (E w) : ℂ)` using `fun w => congrArg Subtype.val (congrFun hF w)`. Establish `hadd : ∀ x y, F (x + y) = F x + F y`.

Introduce `x y`. Establish `hc : Continuous fun y => F (x + y) - F y` using `by fun_prop`. Use `Complex.isCoveringMap_exp.const_of_comp hc (fun y y' => Subtype.ext (by` as an intermediate fact. Simplify using `only [Complex.exp_sub, hF', hEadd, map_mul, Units.val_mul]`. Rewrite using `[mul_div_assoc, mul_div_assoc, div_self (Units.ne_zero _), div_self (Units.ne_zero _)])) y 0`.

Simplify using `only [add_zero, hF0, sub_zero] at this`. Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree. Set `L : ℂ →L[ℝ] ℂ` to `(AddMonoidHom.mk' F hadd).toRealLinearMap F.continuous`. Establish `hL : ∀ w, (ψ (E w) : ℂ) = Complex.exp (L w)` using `fun w => (hF' w).symm`.

Establish `hper : Complex.exp (L (2 * Real.pi * Complex.I)) = 1`. Rewrite using `[← hL]`. Establish `: E (2 * Real.pi * Complex.I) = 1` using `Units.ext Complex.exp_two_pi_mul_I`. Rewrite using `[this, map_one, Units.val_one]`. Take `⟨n, hn⟩` from `Complex.exp_eq_one_iff.1 hper`.

Establish `hLI : L Complex.I = n * Complex.I`. Establish `e : L (2 * Real.pi * Complex.I) = (2 * Real.pi : ℝ) • L Complex.I`. Rewrite using `[← map_smul, Complex.real_smul]`. Use `push_cast`. Put the polynomial expressions in normal form.

Rewrite `hn` using `[e, Complex.real_smul]`. Establish `hpi : (2 * Real.pi : ℂ) ≠ 0`. Conclude with `(mul_ne_zero two_ne_zero Real.pi_ne_zero)` after adjusting the coercions. Move the coercions through the operations in `at hn`. Establish `: (2 * Real.pi : ℂ) * L Complex.I = (2 * Real.pi : ℂ) * (n * Complex.I)` using `by rw [hn]; ring`.

Conclude with `mul_left_cancel₀ hpi this`. Use `⟨L 1, n, fun z => ?_⟩` and prove the remaining obligations. Establish `hz : (z : ℂ) ≠ 0` using `z.ne_zero`. Establish `hnz : ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (norm_ne_zero_iff.2 hz)`. Establish `hEz : E (Complex.log z) = z` using `Units.ext (Complex.exp_log hz)`.

Establish `hlog : Complex.log z = (Real.log ‖(z : ℂ)‖ : ℝ) • (1 : ℂ) + (Complex.arg z : ℝ) • Complex.I`. Rewrite using `[Complex.real_smul, Complex.real_smul, mul_one]`. Both sides reduce to the same expression. Establish `hunit : (z : ℂ) / ‖(z : ℂ)‖ = Complex.exp (Complex.arg z * Complex.I)`. Rewrite using `[div_eq_iff hnz, mul_comm]`.

Conclude with `(Complex.norm_mul_exp_arg_mul_I (z : ℂ)).symm`. Rewrite using `[← hEz, hL, hEz, hunit, ← Complex.exp_int_mul, ← Complex.exp_add, hlog, map_add, map_smul, map_smul, hLI, Complex.real_smul, Complex.real_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem continuous_char_units_complex : ∀ ψ : ℂˣ →* ℂˣ, Continuous ψ → ∃ (s : ℂ) (n : ℤ), ∀ z : ℂˣ,
    (ψ z : ℂ) = Complex.exp (s * Real.log ‖(z : ℂ)‖) * ((z : ℂ) / ‖(z : ℂ)‖) ^ n := by
  intro ψ hψ
  let E : ℂ → ℂˣ := fun w => Units.mk0 (Complex.exp w) (Complex.exp_ne_zero w)
  have hE : Continuous E := by
    refine Units.continuous_iff.2 ⟨Complex.continuous_exp, ?_⟩
    have : (fun w => ((E w)⁻¹ : ℂˣ).val) = fun w => (Complex.exp w)⁻¹ := by
      funext w; simp [E]
    rw [this]
    exact Complex.continuous_exp.inv₀ Complex.exp_ne_zero
  have hEadd : ∀ x y, E (x + y) = E x * E y := fun x y => Units.ext (Complex.exp_add x y)
  have hE0 : E 0 = 1 := Units.ext Complex.exp_zero
  let f : C(ℂ, {z : ℂ // z ≠ 0}) :=
    ⟨fun w => ⟨(ψ (E w) : ℂ), Units.ne_zero _⟩, (Units.continuous_val.comp (hψ.comp hE)).subtype_mk _⟩
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0
    (Subtype.ext (by simp [f, hE0]))
  have hF' : ∀ w, Complex.exp (F w) = (ψ (E w) : ℂ) := fun w => congrArg Subtype.val (congrFun hF w)
  have hadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    have hc : Continuous fun y => F (x + y) - F y := by fun_prop
    have := Complex.isCoveringMap_exp.const_of_comp hc (fun y y' => Subtype.ext (by
      simp only [Complex.exp_sub, hF', hEadd, map_mul, Units.val_mul]
      rw [mul_div_assoc, mul_div_assoc, div_self (Units.ne_zero _), div_self (Units.ne_zero _)])) y 0
    simp only [add_zero, hF0, sub_zero] at this
    rw [← this]; ring
  let L : ℂ →L[ℝ] ℂ := (AddMonoidHom.mk' F hadd).toRealLinearMap F.continuous
  have hL : ∀ w, (ψ (E w) : ℂ) = Complex.exp (L w) := fun w => (hF' w).symm

  have hper : Complex.exp (L (2 * Real.pi * Complex.I)) = 1 := by
    rw [← hL]
    have : E (2 * Real.pi * Complex.I) = 1 := Units.ext Complex.exp_two_pi_mul_I
    rw [this, map_one, Units.val_one]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hper
  have hLI : L Complex.I = n * Complex.I := by
    have e : L (2 * Real.pi * Complex.I) = (2 * Real.pi : ℝ) • L Complex.I := by
      rw [← map_smul, Complex.real_smul]; push_cast; ring_nf
    rw [e, Complex.real_smul] at hn
    have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast (mul_ne_zero two_ne_zero Real.pi_ne_zero)
    push_cast at hn
    have : (2 * Real.pi : ℂ) * L Complex.I = (2 * Real.pi : ℂ) * (n * Complex.I) := by rw [hn]; ring
    exact mul_left_cancel₀ hpi this
  refine ⟨L 1, n, fun z => ?_⟩
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hnz : ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hz)
  have hEz : E (Complex.log z) = z := Units.ext (Complex.exp_log hz)
  have hlog : Complex.log z = (Real.log ‖(z : ℂ)‖ : ℝ) • (1 : ℂ) + (Complex.arg z : ℝ) • Complex.I := by
    rw [Complex.real_smul, Complex.real_smul, mul_one]; rfl
  have hunit : (z : ℂ) / ‖(z : ℂ)‖ = Complex.exp (Complex.arg z * Complex.I) := by
    rw [div_eq_iff hnz, mul_comm]
    exact (Complex.norm_mul_exp_arg_mul_I (z : ℂ)).symm
  rw [← hEz, hL, hEz, hunit, ← Complex.exp_int_mul, ← Complex.exp_add, hlog, map_add, map_smul, map_smul,
    hLI, Complex.real_smul, Complex.real_smul]
  congr 1
  ring

end GlobalTheory

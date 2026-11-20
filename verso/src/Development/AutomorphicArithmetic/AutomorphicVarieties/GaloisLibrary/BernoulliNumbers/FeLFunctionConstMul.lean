import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.GaussMulGaussInv

open Finset UpperTheory.V.Bern

/- English proof (translation)
Simplify using `only [ZMod.LFunction, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma fe_LFunction_const_mul {N : ℕ} [NeZero N] (c : ℂ) (Φ : ZMod N → ℂ) (s : ℂ) :
    ZMod.LFunction (fun j => c * Φ j) s = c * ZMod.LFunction Φ s := by
  simp only [ZMod.LFunction, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Introduce `N _ χ k hχ hk hpar`. Take `⟨m, rfl⟩ : ∃ m, k = m + 1` from `⟨k - 1, by omega⟩`. Use `set g := gaussSum χ ZMod.stdAddChar with hg`. Establish `hinv1 : χ⁻¹ (-1) = χ (-1)`. Rewrite using `[MulChar.inv_apply_eq_inv', hpar, ← inv_pow, inv_neg_one]`.

Establish `hF : ZMod.dft (χ : ZMod N → ℂ) = fun j => (χ (-1) * g) * χ⁻¹ j`. Use function extensionality and compare the values at `j`. Rewrite using `[hχ.fourierTransform_eq_inv_mul_gaussSum, show -j = -1 * j by ring, map_mul, hinv1]`. Expand and normalize the polynomial expressions, which then agree. Establish `hF' : ZMod.dft (fun x => χ (-x)) = fun j => g * χ⁻¹ j`.

Rewrite using `[ZMod.dft_comp_neg]`. Use function extensionality and compare the values at `j`. Rewrite using `[hχ.fourierTransform_eq_inv_mul_gaussSum, neg_neg]`. Expand and normalize the polynomial expressions, which then agree. Establish `hs : ∀ n : ℕ, ((m + 1 : ℕ) : ℂ) ≠ -n`.

Introduce `n h`. Establish `h2` using `congrArg Complex.re h`. Simplify using `at h2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs' : χ 0 = 0 ∨ ((m + 1 : ℕ) : ℂ) ≠ 1`.

Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Use `left`. Apply `χ.map_zero'` to reduce the goal to its premises. Introduce and unpack `rfl`. Establish `h1 : (-1 : ZMod 1) = 1` using `Subsingleton.elim _ _`.

Rewrite `hpar` using `[h1, map_one]`. Evaluate the numerical expressions using `at hpar`. Use `right`. Conclude with `(by omega : m + 1 ≠ 1)` after adjusting the coercions. Establish `hfe` using `ZMod.LFunction_one_sub (χ : ZMod N → ℂ) hs hs'`.

Rewrite `hfe` using `[hF, hF', fe_LFunction_const_mul, fe_LFunction_const_mul]`. Establish `he1 : Complex.exp ((Real.pi : ℂ) * Complex.I * ((m + 1 : ℕ) : ℂ) / 2) = Complex.I ^ (m + 1)`. Rewrite using `[show (Real.pi : ℂ) * Complex.I * ((m + 1 : ℕ) : ℂ) / 2 = ((m + 1 : ℕ) : ℂ) * ((Real.pi : ℂ) / 2 * Complex.I) by ring, Complex.exp_nat_mul, Complex.exp_pi_div_two_mul_I]`. Establish `he2 : Complex.exp (-(Real.pi : ℂ) * Complex.I * ((m + 1 : ℕ) : ℂ) / 2) = (-Complex.I) ^ (m + 1)`. Rewrite using `[show -(Real.pi : ℂ) * Complex.I * ((m + 1 : ℕ) : ℂ) / 2 = ((m + 1 : ℕ) : ℂ) * (-(Real.pi : ℂ) / 2 * Complex.I) by ring, Complex.exp_nat_mul, Complex.exp_neg_pi_div_two_mul_I]`.

Establish `hGam : Complex.Gamma ((m + 1 : ℕ) : ℂ) = (m.factorial : ℂ)`. Rewrite using `[Nat.cast_succ, Complex.Gamma_nat_eq_factorial]`. Establish `h2pi : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ)` using `by push_cast; ring`. Establish `key : ZMod.LFunction (χ : ZMod N → ℂ) (1 - ((m + 1 : ℕ) : ℂ)) = (N : ℂ) ^ (((m + 1 : ℕ) : ℂ) - 1) * ((2 * Real.pi : ℝ) : ℂ) ^ (-((m + 1 : ℕ) : ℂ)) * (m.factorial : ℂ) * g * ZMod.LFunction ⇑(χ⁻¹) ((m + 1 : ℕ) : ℂ) * (2 * (-Complex.I) ^ (m + 1))`. Rewrite using `[hfe, he1, he2, hGam, hpar, ← h2pi, neg_pow Complex.I]`.

Expand and normalize the polynomial expressions, which then agree. Use `show ‖ZMod.LFunction (χ : ZMod N → ℂ) (1 - ((m + 1 : ℕ) : ℂ))‖ = _`. Rewrite using `[key]`. Establish `hNpos : (0 : ℝ) < N` using `by exact_mod_cast NeZero.pos N`. Rewrite using `[norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos (NeZero.pos N), Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), (b_gauss χ hχ).1]`.

Simplify using `only [norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, mul_one, Complex.norm_natCast]`. Establish `hre1 : (((m + 1 : ℕ) : ℂ) - 1).re = ((m : ℕ) : ℝ)` using `by simp`. Establish `hre2 : (-((m + 1 : ℕ) : ℂ)).re = -((m + 1 : ℕ) : ℝ)` using `by simp`. Establish `hL : DirichletCharacter.LFunction χ⁻¹ ((m + 1 : ℕ) : ℂ) = ZMod.LFunction ⇑(χ⁻¹) ((m + 1 : ℕ) : ℂ)` using `rfl`. Establish `hNr : (N : ℝ) ^ (((m + 1 : ℕ) : ℝ) - 1 / 2) = (N : ℝ) ^ m * √(N : ℝ)`.

Rewrite using `[Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hNpos]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hre1, hre2, Real.rpow_neg (by positivity), Real.rpow_natCast, Real.rpow_natCast, hL, hNr, Nat.add_sub_cancel, Complex.norm_two]`.

Establish `hpi : (0 : ℝ) < (2 * Real.pi) ^ (m + 1)` using `by positivity`. Clear the denominators using the available nonvanishing facts.
-/
theorem UpperTheory.V.Bern.b_fe :
    ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (k : ℕ), χ.IsPrimitive → 1 ≤ k → χ (-1) = (-1) ^ k → ‖χ.LFunction (1 - k)‖ = 2 * ((k - 1).factorial : ℝ) * (N : ℝ) ^ ((k : ℝ) - 1 / 2) / (2 * Real.pi) ^ k * ‖χ⁻¹.LFunction k‖ := by
  intro N _ χ k hχ hk hpar
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  set g := gaussSum χ ZMod.stdAddChar with hg
  have hinv1 : χ⁻¹ (-1) = χ (-1) := by
    rw [MulChar.inv_apply_eq_inv', hpar, ← inv_pow, inv_neg_one]
  have hF : ZMod.dft (χ : ZMod N → ℂ) = fun j => (χ (-1) * g) * χ⁻¹ j := by
    funext j
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, show -j = -1 * j by ring, map_mul, hinv1]
    ring
  have hF' : ZMod.dft (fun x => χ (-x)) = fun j => g * χ⁻¹ j := by
    rw [ZMod.dft_comp_neg]
    funext j
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, neg_neg]
    ring
  have hs : ∀ n : ℕ, ((m + 1 : ℕ) : ℂ) ≠ -n := by
    intro n h
    have h2 := congrArg Complex.re h
    simp at h2
    linarith
  have hs' : χ 0 = 0 ∨ ((m + 1 : ℕ) : ℂ) ≠ 1 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · left
      apply χ.map_zero'
      rintro rfl
      have h1 : (-1 : ZMod 1) = 1 := Subsingleton.elim _ _
      rw [h1, map_one] at hpar
      norm_num at hpar
    · right
      exact_mod_cast (by omega : m + 1 ≠ 1)
  have hfe := ZMod.LFunction_one_sub (χ : ZMod N → ℂ) hs hs'
  rw [hF, hF', fe_LFunction_const_mul, fe_LFunction_const_mul] at hfe
  have he1 : Complex.exp ((Real.pi : ℂ) * Complex.I * ((m + 1 : ℕ) : ℂ) / 2) = Complex.I ^ (m + 1) := by
    rw [show (Real.pi : ℂ) * Complex.I * ((m + 1 : ℕ) : ℂ) / 2
        = ((m + 1 : ℕ) : ℂ) * ((Real.pi : ℂ) / 2 * Complex.I) by ring,
      Complex.exp_nat_mul, Complex.exp_pi_div_two_mul_I]
  have he2 : Complex.exp (-(Real.pi : ℂ) * Complex.I * ((m + 1 : ℕ) : ℂ) / 2) = (-Complex.I) ^ (m + 1) := by
    rw [show -(Real.pi : ℂ) * Complex.I * ((m + 1 : ℕ) : ℂ) / 2
        = ((m + 1 : ℕ) : ℂ) * (-(Real.pi : ℂ) / 2 * Complex.I) by ring,
      Complex.exp_nat_mul, Complex.exp_neg_pi_div_two_mul_I]
  have hGam : Complex.Gamma ((m + 1 : ℕ) : ℂ) = (m.factorial : ℂ) := by
    rw [Nat.cast_succ, Complex.Gamma_nat_eq_factorial]
  have h2pi : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  have key : ZMod.LFunction (χ : ZMod N → ℂ) (1 - ((m + 1 : ℕ) : ℂ)) =
      (N : ℂ) ^ (((m + 1 : ℕ) : ℂ) - 1) * ((2 * Real.pi : ℝ) : ℂ) ^ (-((m + 1 : ℕ) : ℂ)) *
        (m.factorial : ℂ) * g * ZMod.LFunction ⇑(χ⁻¹) ((m + 1 : ℕ) : ℂ) *
        (2 * (-Complex.I) ^ (m + 1)) := by
    rw [hfe, he1, he2, hGam, hpar, ← h2pi, neg_pow Complex.I]
    ring
  show ‖ZMod.LFunction (χ : ZMod N → ℂ) (1 - ((m + 1 : ℕ) : ℂ))‖ = _
  rw [key]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul,
    Complex.norm_natCast_cpow_of_pos (NeZero.pos N),
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), (b_gauss χ hχ).1]
  simp only [norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, mul_one, Complex.norm_natCast]
  have hre1 : (((m + 1 : ℕ) : ℂ) - 1).re = ((m : ℕ) : ℝ) := by simp
  have hre2 : (-((m + 1 : ℕ) : ℂ)).re = -((m + 1 : ℕ) : ℝ) := by simp
  have hL : DirichletCharacter.LFunction χ⁻¹ ((m + 1 : ℕ) : ℂ) = ZMod.LFunction ⇑(χ⁻¹) ((m + 1 : ℕ) : ℂ) := rfl
  have hNr : (N : ℝ) ^ (((m + 1 : ℕ) : ℝ) - 1 / 2) = (N : ℝ) ^ m * √(N : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hNpos]
    congr 1
    push_cast
    ring
  rw [hre1, hre2, Real.rpow_neg (by positivity), Real.rpow_natCast, Real.rpow_natCast, hL, hNr,
    Nat.add_sub_cancel, Complex.norm_two]
  have hpi : (0 : ℝ) < (2 * Real.pi) ^ (m + 1) := by positivity
  field_simp

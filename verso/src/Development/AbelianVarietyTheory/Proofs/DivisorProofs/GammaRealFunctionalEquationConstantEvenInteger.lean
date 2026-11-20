import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `d hd f s hs A B hAB`. Use `set k : ℂ := ((2 * s : ℕ) : ℂ) with hk`. Establish `hk' : k = 2 * (s : ℂ)` using `by rw [hk]; push_cast; ring`. Establish `hh : Complex.Gammaℝ (1 - k) ≠ 0`. Rewrite using `[Ne, Complex.Gammaℝ_eq_zero_iff]`.

Introduce and unpack `⟨n, hn⟩`. Establish `h1 : ((1 : ℤ) : ℂ) = ((2 * s - 2 * n : ℤ) : ℂ)` using `by push_cast; rw [hk'] at hn; linear_combination hn`. Establish `h2` using `Int.cast_injective h1`. Use linear arithmetic over natural numbers and integers. Establish `hodd : ∀ n : ℕ, k ≠ -(2 * n + 1)`.

Introduce `n hn`. Establish `h1 : ((2 * s : ℤ) : ℂ) = ((-(2 * n + 1) : ℤ) : ℂ)` using `by push_cast; rw [← hk']; exact hn`. Establish `h2` using `Int.cast_injective h1`. Use linear arithmetic over natural numbers and integers. Establish `hratio` using `Complex.Gammaℝ_div_Gammaℝ_one_sub hodd`.

Establish `hΓ : Complex.Gamma k = (((2 * s - 1).factorial : ℕ) : ℂ)`. Establish `: k = ((2 * s - 1 : ℕ) : ℂ) + 1`. Rewrite using `[hk]`. Use `norm_cast`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[this, Complex.Gamma_nat_eq_factorial]`. Establish `hcos : Complex.cos ((Real.pi : ℂ) * k / 2) = (-1) ^ s`. Rewrite using `[hk', show (Real.pi : ℂ) * (2 * s) / 2 = (s : ℂ) * Real.pi by ring]`. Rewrite using `[show (s : ℂ) * Real.pi = (((s : ℝ) * Real.pi : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos, Real.cos_nat_mul_pi]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hpow : (2 * (Real.pi : ℂ)) ^ (-k) = ((2 * (Real.pi : ℂ)) ^ (2 * s))⁻¹`. Rewrite using `[Complex.cpow_neg, hk, Complex.cpow_natCast]`. Establish `hg : Complex.Gammaℝ k = Complex.Gammaℝ (1 - k) * (2 * ((2 * (Real.pi : ℂ)) ^ (2 * s))⁻¹ * (((2 * s - 1).factorial : ℕ) : ℂ) * (-1) ^ s)`. Rewrite `hratio` using `[div_eq_iff hh, Complex.Gammaℂ_def, hΓ, hcos, hpow]`.

Rewrite using `[hratio]`. Expand and normalize the polynomial expressions, which then agree. Establish `hd0 : (d : ℂ) ≠ 0` using `by exact_mod_cast hd.ne'`. Establish `hE : ((d ^ (((2 * s : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) = (d : ℂ) ^ (k - 1 / 2)`. Rewrite using `[Complex.ofReal_cpow hd.le]`.

Use `congr 1`. Rewrite using `[hk]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hD : (d : ℂ) ^ (k / 2) = (d : ℂ) ^ ((1 - k) / 2) * (d : ℂ) ^ (k - 1 / 2)`.

Rewrite using `[← Complex.cpow_add _ _ hd0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hD2 : (d : ℂ) ^ ((1 - k) / 2) ≠ 0`. Rewrite using `[Ne, Complex.cpow_eq_zero_iff]`.

The claim follows by propositional logic. Establish `hB : B = (d : ℂ) ^ (k - 1 / 2) * (2 * ((2 * (Real.pi : ℂ)) ^ (2 * s))⁻¹ * (((2 * s - 1).factorial : ℕ) : ℂ) * (-1) ^ s) ^ f * A`. Rewrite `hAB` using `[hD, hg, mul_pow]`. Establish `hne : (d : ℂ) ^ ((1 - k) / 2) * Complex.Gammaℝ (1 - k) ^ f ≠ 0` using `mul_ne_zero hD2 (pow_ne_zero _ hh)`. Apply `mul_left_cancel₀ hne` to reduce the goal to its premises.

Rewrite using `[← hAB]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hE, hB]`. Establish `hI : (2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * f) = ((2 * (Real.pi : ℂ)) ^ (2 * s)) ^ f * ((-1 : ℂ) ^ s) ^ f`. Rewrite using `[pow_mul, ← mul_pow, mul_pow (2 * (Real.pi : ℂ)) Complex.I, pow_mul Complex.I 2 s, Complex.I_sq]`.

Establish `hm : (((-1 : ℂ) ^ s) ^ f)⁻¹ = ((-1 : ℂ) ^ s) ^ f`. Rewrite using `[← inv_pow, ← inv_pow, inv_neg_one]`. Rewrite using `[hI, mul_inv, hm, ← inv_pow]`. Establish `h2 : (2 : ℂ)⁻¹ ^ f * (2 : ℂ) ^ f = 1`. Rewrite using `[← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]`.

Take the linear combination `(-((((2 * s - 1).factorial : ℕ) : ℂ) ^ f * (d : ℂ) ^ (k - 1 / 2) * (((2 * (Real.pi : ℂ)) ^ (2 * s))⁻¹) ^ f * ((-1 : ℂ) ^ s) ^ f * A)) * h2`.
-/
theorem gammaℝ_functional_constant_even :
    ∀ (d : ℝ), 0 < d → ∀ (f s : ℕ), 1 ≤ s → ∀ A B : ℂ,
      (d : ℂ) ^ (((2 * s : ℕ) : ℂ) / 2) * Complex.Gammaℝ ((2 * s : ℕ) : ℂ) ^ f * A =
        (d : ℂ) ^ ((1 - ((2 * s : ℕ) : ℂ)) / 2) * Complex.Gammaℝ (1 - ((2 * s : ℕ) : ℂ)) ^ f * B →
      (((2 * s - 1).factorial : ℕ) : ℂ) ^ f * ((d ^ (((2 * s : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) *
        ((2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * f))⁻¹ * A = (2 : ℂ)⁻¹ ^ f * B := by
  intro d hd f s hs A B hAB
  set k : ℂ := ((2 * s : ℕ) : ℂ) with hk
  have hk' : k = 2 * (s : ℂ) := by rw [hk]; push_cast; ring
  have hh : Complex.Gammaℝ (1 - k) ≠ 0 := by
    rw [Ne, Complex.Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    have h1 : ((1 : ℤ) : ℂ) = ((2 * s - 2 * n : ℤ) : ℂ) := by
      push_cast; rw [hk'] at hn; linear_combination hn
    have h2 := Int.cast_injective h1
    omega
  have hodd : ∀ n : ℕ, k ≠ -(2 * n + 1) := by
    intro n hn
    have h1 : ((2 * s : ℤ) : ℂ) = ((-(2 * n + 1) : ℤ) : ℂ) := by
      push_cast; rw [← hk']; exact hn
    have h2 := Int.cast_injective h1
    omega
  have hratio := Complex.Gammaℝ_div_Gammaℝ_one_sub hodd
  have hΓ : Complex.Gamma k = (((2 * s - 1).factorial : ℕ) : ℂ) := by
    have : k = ((2 * s - 1 : ℕ) : ℂ) + 1 := by
      rw [hk]; norm_cast; omega
    rw [this, Complex.Gamma_nat_eq_factorial]
  have hcos : Complex.cos ((Real.pi : ℂ) * k / 2) = (-1) ^ s := by
    rw [hk', show (Real.pi : ℂ) * (2 * s) / 2 = (s : ℂ) * Real.pi by ring]
    rw [show (s : ℂ) * Real.pi = (((s : ℝ) * Real.pi : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cos, Real.cos_nat_mul_pi]
    push_cast; ring
  have hpow : (2 * (Real.pi : ℂ)) ^ (-k) = ((2 * (Real.pi : ℂ)) ^ (2 * s))⁻¹ := by
    rw [Complex.cpow_neg, hk, Complex.cpow_natCast]
  have hg : Complex.Gammaℝ k = Complex.Gammaℝ (1 - k) *
      (2 * ((2 * (Real.pi : ℂ)) ^ (2 * s))⁻¹ * (((2 * s - 1).factorial : ℕ) : ℂ) * (-1) ^ s) := by
    rw [div_eq_iff hh, Complex.Gammaℂ_def, hΓ, hcos, hpow] at hratio
    rw [hratio]; ring
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hE : ((d ^ (((2 * s : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) = (d : ℂ) ^ (k - 1 / 2) := by
    rw [Complex.ofReal_cpow hd.le]; congr 1; rw [hk]; push_cast; ring
  have hD : (d : ℂ) ^ (k / 2) = (d : ℂ) ^ ((1 - k) / 2) * (d : ℂ) ^ (k - 1 / 2) := by
    rw [← Complex.cpow_add _ _ hd0]; congr 1; ring
  have hD2 : (d : ℂ) ^ ((1 - k) / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have hB : B = (d : ℂ) ^ (k - 1 / 2) *
      (2 * ((2 * (Real.pi : ℂ)) ^ (2 * s))⁻¹ * (((2 * s - 1).factorial : ℕ) : ℂ) * (-1) ^ s) ^ f * A := by
    rw [hD, hg, mul_pow] at hAB
    have hne : (d : ℂ) ^ ((1 - k) / 2) * Complex.Gammaℝ (1 - k) ^ f ≠ 0 :=
      mul_ne_zero hD2 (pow_ne_zero _ hh)
    apply mul_left_cancel₀ hne
    rw [← hAB]; ring
  rw [hE, hB]
  have hI : (2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * f) =
      ((2 * (Real.pi : ℂ)) ^ (2 * s)) ^ f * ((-1 : ℂ) ^ s) ^ f := by
    rw [pow_mul, ← mul_pow, mul_pow (2 * (Real.pi : ℂ)) Complex.I, pow_mul Complex.I 2 s, Complex.I_sq]
  have hm : (((-1 : ℂ) ^ s) ^ f)⁻¹ = ((-1 : ℂ) ^ s) ^ f := by
    rw [← inv_pow, ← inv_pow, inv_neg_one]
  rw [hI, mul_inv, hm, ← inv_pow]
  have h2 : (2 : ℂ)⁻¹ ^ f * (2 : ℂ) ^ f = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
  linear_combination (-((((2 * s - 1).factorial : ℕ) : ℂ) ^ f * (d : ℂ) ^ (k - 1 / 2) *
    (((2 * (Real.pi : ℂ)) ^ (2 * s))⁻¹) ^ f * ((-1 : ℂ) ^ s) ^ f * A)) * h2

end GlobalTheory

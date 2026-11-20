import Mathlib

noncomputable section

open Complex

namespace PositivityTheory.Rg.Sw.Glob.VacE

/- English proof (translation)
Establish `hcC : (c : ℂ) ≠ 0` using `by exact_mod_cast hc.ne'`. Establish `hco' : (co : ℂ) ≠ 0` using `by exact_mod_cast hco.ne'`. Establish `htC : (t : ℂ) ^ 2 = (c : ℂ) ^ 2` using `by exact_mod_cast ht`. Establish `hσC : (σ : ℂ) ^ 2 = 1` using `by exact_mod_cast hσ`. Establish `hs2 : (si : ℂ) ^ 2 + (co : ℂ) ^ 2 = 1` using `by exact_mod_cast hs`.

Establish `hden : (c : ℂ) * co - I * t * σ * si ≠ 0`. Introduce `h0`. Use `congrArg Complex.re h0` as an intermediate fact. Simplify using `at this`. Break down `this with h | h` into its components or cases.

Conclude with `hc.ne' h`. Conclude with `hco.ne' h`. Simplify using `only [Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div]`. Rewrite using `[neg_sq, htC, hσC]`. Establish `e1 : (c : ℂ) ^ 2 * 1 / ((c : ℂ) * ((co : ℂ))⁻¹ ^ 2) - I * t * σ * (si * co) = co * ((c : ℂ) * co - I * t * σ * si)`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e1]`. Clear the denominators using the available nonvanishing facts. Establish `htσ : (t : ℂ) ^ 2 * (σ : ℂ) ^ 2 = (c : ℂ) ^ 2` using `by rw [htC, hσC, mul_one]`. Take the linear combination `(-(c : ℂ) ^ 2) * hs2 + (si : ℂ) ^ 2 * I ^ 2 * htσ + (si : ℂ) ^ 2 * (c : ℂ) ^ 2 * Complex.I_sq`.
-/
theorem coord_gamma (c t σ co si : ℝ) (hc : 0 < c) (ht : t ^ 2 = c ^ 2) (hσ : σ ^ 2 = 1) (hco : 0 < co)
    (hs : si ^ 2 + co ^ 2 = 1) :
    (t : ℂ) ^ 2 * (σ : ℂ) ^ 2 /
        (((-t : ℝ) : ℂ) ^ 2 * (σ : ℂ) ^ 2 / ((c : ℂ) * ((co⁻¹ : ℝ) : ℂ) ^ 2) - I * t * σ * ((si * co : ℝ) : ℂ)) -
      I * t * σ * ((si / co : ℝ) : ℂ) = c := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hco' : (co : ℂ) ≠ 0 := by exact_mod_cast hco.ne'
  have htC : (t : ℂ) ^ 2 = (c : ℂ) ^ 2 := by exact_mod_cast ht
  have hσC : (σ : ℂ) ^ 2 = 1 := by exact_mod_cast hσ
  have hs2 : (si : ℂ) ^ 2 + (co : ℂ) ^ 2 = 1 := by exact_mod_cast hs
  have hden : (c : ℂ) * co - I * t * σ * si ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    rcases this with h | h
    · exact hc.ne' h
    · exact hco.ne' h
  simp only [Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div]
  rw [neg_sq, htC, hσC]
  have e1 : (c : ℂ) ^ 2 * 1 / ((c : ℂ) * ((co : ℂ))⁻¹ ^ 2) - I * t * σ * (si * co) = co * ((c : ℂ) * co - I * t * σ * si) := by
    field_simp
  rw [e1]
  field_simp
  have htσ : (t : ℂ) ^ 2 * (σ : ℂ) ^ 2 = (c : ℂ) ^ 2 := by rw [htC, hσC, mul_one]
  linear_combination (-(c : ℂ) ^ 2) * hs2 + (si : ℂ) ^ 2 * I ^ 2 * htσ + (si : ℂ) ^ 2 * (c : ℂ) ^ 2 * Complex.I_sq

/- English proof (translation)
Establish `hcC : (c : ℂ) ≠ 0` using `by exact_mod_cast hc.ne'`. Establish `hco' : (co : ℂ) ≠ 0` using `by exact_mod_cast hco.ne'`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `htC : (t : ℂ) ^ 2 = (c : ℂ) ^ 2` using `by exact_mod_cast ht`. Establish `hσC : (σ : ℂ) ^ 2 = 1` using `by exact_mod_cast hσ`.

Establish `hs2 : (si : ℂ) ^ 2 + (co : ℂ) ^ 2 = 1` using `by exact_mod_cast hs`. Establish `habs : ((|t| : ℝ) : ℂ) ^ 2 = (c : ℂ) ^ 2`. Rewrite using `[← Complex.ofReal_pow, sq_abs]`. Conclude with `ht` after adjusting the coercions. Establish `hden : (c : ℂ) * co - I * t * σ * si ≠ 0`.

Introduce `h0`. Use `congrArg Complex.re h0` as an intermediate fact. Simplify using `at this`. Break down `this with h | h` into its components or cases. Conclude with `hc.ne' h`.

Conclude with `hco.ne' h`. Simplify using `only [Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div]`. Rewrite using `[neg_sq, htC, hσC, div_pow, habs]`. Establish `e1 : (c : ℂ) ^ 2 * 1 / ((c : ℂ) * ((co : ℂ))⁻¹ ^ 2) - I * t * σ * (si * co) = co * ((c : ℂ) * co - I * t * σ * si)`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e1]`. Establish `key : (co : ℂ)⁻¹ * ((Real.pi : ℂ) / ((c : ℂ) * (co : ℂ)⁻¹ ^ 2)) * ((Real.pi : ℂ) / (co * ((c : ℂ) * co - I * t * σ * si))) * ((c : ℂ) ^ 2 / (Real.pi : ℂ) ^ 2) = (c : ℂ) / ((c : ℂ) * co - I * t * σ * si)`. Clear the denominators using the available nonvanishing facts. Rewrite using `[key, div_eq_iff hden]`. Establish `htσ : (t : ℂ) ^ 2 * (σ : ℂ) ^ 2 = (c : ℂ) ^ 2` using `by rw [htC, hσC, mul_one]`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `(-(c : ℂ) ^ 2) * hs2 + (si : ℂ) ^ 2 * I ^ 2 * htσ + (si : ℂ) ^ 2 * (c : ℂ) ^ 2 * Complex.I_sq`.
-/
theorem coord_const (c t σ co si : ℝ) (hc : 0 < c) (ht : t ^ 2 = c ^ 2) (hσ : σ ^ 2 = 1) (hco : 0 < co)
    (hs : si ^ 2 + co ^ 2 = 1) :
    ((co⁻¹ : ℝ) : ℂ) * ((Real.pi : ℂ) / ((c : ℂ) * ((co⁻¹ : ℝ) : ℂ) ^ 2)) *
        ((Real.pi : ℂ) / (((-t : ℝ) : ℂ) ^ 2 * (σ : ℂ) ^ 2 / ((c : ℂ) * ((co⁻¹ : ℝ) : ℂ) ^ 2) -
          I * t * σ * ((si * co : ℝ) : ℂ))) * (((|t| / Real.pi : ℝ) : ℂ)) ^ 2 =
      co + I * (σ * t / c) * si := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hco' : (co : ℂ) ≠ 0 := by exact_mod_cast hco.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have htC : (t : ℂ) ^ 2 = (c : ℂ) ^ 2 := by exact_mod_cast ht
  have hσC : (σ : ℂ) ^ 2 = 1 := by exact_mod_cast hσ
  have hs2 : (si : ℂ) ^ 2 + (co : ℂ) ^ 2 = 1 := by exact_mod_cast hs
  have habs : ((|t| : ℝ) : ℂ) ^ 2 = (c : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, sq_abs]; exact_mod_cast ht
  have hden : (c : ℂ) * co - I * t * σ * si ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    rcases this with h | h
    · exact hc.ne' h
    · exact hco.ne' h
  simp only [Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div]
  rw [neg_sq, htC, hσC, div_pow, habs]
  have e1 : (c : ℂ) ^ 2 * 1 / ((c : ℂ) * ((co : ℂ))⁻¹ ^ 2) - I * t * σ * (si * co) = co * ((c : ℂ) * co - I * t * σ * si) := by
    field_simp
  rw [e1]
  have key : (co : ℂ)⁻¹ * ((Real.pi : ℂ) / ((c : ℂ) * (co : ℂ)⁻¹ ^ 2)) *
      ((Real.pi : ℂ) / (co * ((c : ℂ) * co - I * t * σ * si))) * ((c : ℂ) ^ 2 / (Real.pi : ℂ) ^ 2) =
      (c : ℂ) / ((c : ℂ) * co - I * t * σ * si) := by
    field_simp
  rw [key, div_eq_iff hden]
  have htσ : (t : ℂ) ^ 2 * (σ : ℂ) ^ 2 = (c : ℂ) ^ 2 := by rw [htC, hσC, mul_one]
  field_simp
  linear_combination (-(c : ℂ) ^ 2) * hs2 + (si : ℂ) ^ 2 * I ^ 2 * htσ + (si : ℂ) ^ 2 * (c : ℂ) ^ 2 * Complex.I_sq

end PositivityTheory.Rg.Sw.Glob.VacE

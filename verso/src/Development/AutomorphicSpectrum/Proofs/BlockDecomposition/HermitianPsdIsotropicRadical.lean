import Mathlib

namespace GlobalTheory.CompanionTheory.HermitianForm

/- English proof (translation)
Establish `hb : 0 ≤ (B u u).re` using `hpos u`. Establish `key : ∀ t : ℝ, 0 ≤ 2 * t * (B v u).re + t ^ 2 * (B u u).re`. Introduce `t`. Establish `h` using `hpos (v + (t : ℂ) • u)`. Establish `e : B (v + (t : ℂ) • u) (v + (t : ℂ) • u) = B v v + (t : ℂ) * B v u + (t : ℂ) * B u v + (t : ℂ) * (t : ℂ) * B u u`.

Simplify using `only [map_add, LinearMap.add_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Complex.conj_ofReal]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[e, hv, hB v u]`. Simplify using `only [zero_add, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.mul_im, zero_mul, sub_zero, add_zero] at h`. Use polynomial arithmetic with `[h]`.

Use `set a := (B v u).re with ha`. Use `set b := (B u u).re with hb'`. Establish `hb1 : 0 < b + 1` using `by linarith`. Establish `h` using `key (-a / (b + 1))`. Establish `e2 : 2 * (-a / (b + 1)) * a + (-a / (b + 1)) ^ 2 * b = -(a ^ 2 * (b + 2)) / (b + 1) ^ 2`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[e2]`. Establish `h3 : 0 ≤ -(a ^ 2 * (b + 2))`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Establish `: -(a ^ 2 * (b + 2)) / (b + 1) ^ 2 < 0` using `div_neg_of_neg_of_pos hc (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : a ^ 2 * (b + 2) ≤ 0` using `by linarith`. Establish `h5 : a ^ 2 ≤ 0`.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Establish `: 0 < a ^ 2 * (b + 2)` using `mul_pos hc (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h6 : a ^ 2 = 0` using `le_antisymm h5 (sq_nonneg a)`.

Conclude with `pow_eq_zero_iff (two_ne_zero) |>.mp h6`.
-/
theorem re_pairing_eq_zero_of_psd {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : ∀ v w, B w v = starRingEnd ℂ (B v w))
    (hpos : ∀ v, 0 ≤ (B v v).re) (v : V) (hv : B v v = 0) (u : V) : (B v u).re = 0 := by
  have hb : 0 ≤ (B u u).re := hpos u
  have key : ∀ t : ℝ, 0 ≤ 2 * t * (B v u).re + t ^ 2 * (B u u).re := by
    intro t
    have h := hpos (v + (t : ℂ) • u)
    have e : B (v + (t : ℂ) • u) (v + (t : ℂ) • u)
        = B v v + (t : ℂ) * B v u + (t : ℂ) * B u v + (t : ℂ) * (t : ℂ) * B u u := by
      simp only [map_add, LinearMap.add_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, Complex.conj_ofReal]
      ring
    rw [e, hv, hB v u] at h
    simp only [zero_add, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.mul_im, zero_mul, sub_zero, add_zero] at h
    nlinarith [h]
  set a := (B v u).re with ha
  set b := (B u u).re with hb'
  have hb1 : 0 < b + 1 := by linarith
  have h := key (-a / (b + 1))
  have e2 : 2 * (-a / (b + 1)) * a + (-a / (b + 1)) ^ 2 * b
      = -(a ^ 2 * (b + 2)) / (b + 1) ^ 2 := by
    field_simp
    ring
  rw [e2] at h
  have h3 : 0 ≤ -(a ^ 2 * (b + 2)) := by
    by_contra hc
    push Not at hc
    have : -(a ^ 2 * (b + 2)) / (b + 1) ^ 2 < 0 := div_neg_of_neg_of_pos hc (by positivity)
    linarith
  have h4 : a ^ 2 * (b + 2) ≤ 0 := by linarith
  have h5 : a ^ 2 ≤ 0 := by
    by_contra hc
    push Not at hc
    have : 0 < a ^ 2 * (b + 2) := mul_pos hc (by linarith)
    linarith
  have h6 : a ^ 2 = 0 := le_antisymm h5 (sq_nonneg a)
  exact pow_eq_zero_iff (two_ne_zero) |>.mp h6

/- English proof (translation)
Introduce `V _ _ B hB hpos v hv w`. Establish `hre` using `re_pairing_eq_zero_of_psd B hB hpos v hv w`. Establish `him` using `re_pairing_eq_zero_of_psd B hB hpos v hv (Complex.I • w)`. Establish `e : B v (Complex.I • w) = -Complex.I * B v w`. Simplify using `only [map_smulₛₗ, smul_eq_mul, Complex.conj_I]`.

Rewrite `him` using `[e]`. Simplify using `only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] at him`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `using hre`. Simplify using `using him`.
-/
theorem pairing_eq_zero_of_psd : ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ v w, B w v = starRingEnd ℂ (B v w)) →
    (∀ v, 0 ≤ (B v v).re) → ∀ v, B v v = 0 → ∀ w, B v w = 0 := by
  intro V _ _ B hB hpos v hv w
  have hre := re_pairing_eq_zero_of_psd B hB hpos v hv w
  have him := re_pairing_eq_zero_of_psd B hB hpos v hv (Complex.I • w)
  have e : B v (Complex.I • w) = -Complex.I * B v w := by
    simp only [map_smulₛₗ, smul_eq_mul, Complex.conj_I]
  rw [e] at him
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] at him
  apply Complex.ext
  · simpa using hre
  · simpa using him

end GlobalTheory.CompanionTheory.HermitianForm

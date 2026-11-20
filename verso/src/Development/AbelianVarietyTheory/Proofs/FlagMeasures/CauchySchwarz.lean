import Mathlib
open scoped ComplexOrder

namespace GlobalTheory.HermitianCauchySchwarz

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Establish `h1` using `hI (x + y)`. Establish `h2` using `hI (x + Complex.I • y)`. Establish `hx` using `hI x`. Establish `hy` using `hI y`. Rewrite `h1`, `h2`, `hx`, `hy` using `[Complex.nonneg_iff]`.

Simplify using `only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im, RingHom.id_apply] at h1 h2`. Apply the tactic sequence `apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im] <;> linarith [h1.2, h2.2, hx.2, hy.2]`.
-/
theorem herm (I : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hI : ∀ x : V, (0 : ℂ) ≤ I x x) (x y : V) :
    I y x = starRingEnd ℂ (I x y) := by
  have h1 := hI (x + y)
  have h2 := hI (x + Complex.I • y)
  have hx := hI x
  have hy := hI y
  rw [Complex.nonneg_iff] at h1 h2 hx hy
  simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.I_re, Complex.I_im, RingHom.id_apply] at h1 h2
  apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im] <;> linarith [h1.2, h2.2, hx.2, hy.2]

/- English proof (translation)
Use `set b := I x y with hb`. Establish `hyx` using `herm I hI x y`. Establish `hx` using `(Complex.nonneg_iff.mp (hI x))`. Establish `hy` using `(Complex.nonneg_iff.mp (hI y))`. Establish `hq : ∀ s : ℝ, 0 ≤ ((I y y).re * (b.re * b.re + b.im * b.im)) * (s * s) + (-2 * (b.re * b.re + b.im * b.im)) * s + (I x x).re`.

Introduce `s`. Establish `h` using `(Complex.nonneg_iff.mp (hI (x + ((-(s : ℂ)) * starRingEnd ℂ b) • y))).1`. Simplify using `only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply] at h`. Rewrite `h` using `[hyx]`. Simplify using `only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, map_mul, map_neg, Complex.conj_ofReal, RingHom.map_neg, Complex.conj_conj, ← hb, Complex.add_im, mul_zero, sub_zero, neg_z …`.

Rewrite `h` using `[← hy.2]`. Use polynomial arithmetic with `[h, hx.2, hy.2]`. Establish `hd` using `discrim_le_zero hq`. Unfold `discrim at hd`. Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`.

Use `set n := b.re * b.re + b.im * b.im`. Establish `hn : 0 ≤ n` using `by nlinarith [mul_self_nonneg b.re, mul_self_nonneg b.im]`. Establish `hac : 0 ≤ (I x x).re * (I y y).re` using `mul_nonneg hx.1 hy.1`. Break down `hn.eq_or_lt with h0 | hpos` into its components or cases. Rewrite using `[← h0]`.

Conclude with `hac`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem cauchy_schwarz (I : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hI : ∀ x : V, (0 : ℂ) ≤ I x x) (x y : V) :
    ‖I x y‖ ^ 2 ≤ (I x x).re * (I y y).re := by
  set b := I x y with hb
  have hyx := herm I hI x y
  have hx := (Complex.nonneg_iff.mp (hI x))
  have hy := (Complex.nonneg_iff.mp (hI y))
  have hq : ∀ s : ℝ, 0 ≤ ((I y y).re * (b.re * b.re + b.im * b.im)) * (s * s)
      + (-2 * (b.re * b.re + b.im * b.im)) * s + (I x x).re := by
    intro s
    have h := (Complex.nonneg_iff.mp (hI (x + ((-(s : ℂ)) * starRingEnd ℂ b) • y))).1
    simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply] at h
    rw [hyx] at h
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, map_mul, map_neg,
      Complex.conj_ofReal, RingHom.map_neg, Complex.conj_conj, ← hb, Complex.add_im, mul_zero,
      sub_zero, neg_zero, zero_mul, add_zero] at h
    rw [← hy.2] at h
    nlinarith [h, hx.2, hy.2]
  have hd := discrim_le_zero hq
  unfold discrim at hd
  rw [Complex.sq_norm, Complex.normSq_apply]
  set n := b.re * b.re + b.im * b.im
  have hn : 0 ≤ n := by nlinarith [mul_self_nonneg b.re, mul_self_nonneg b.im]
  have hac : 0 ≤ (I x x).re * (I y y).re := mul_nonneg hx.1 hy.1
  rcases hn.eq_or_lt with h0 | hpos
  · rw [← h0]; exact hac
  · nlinarith

end GlobalTheory.HermitianCauchySchwarz

/- English proof (translation)
Introduce `I hI x y` and use `GlobalTheory.HermitianCauchySchwarz.cauchy_schwarz I hI x y`.
-/
theorem GlobalTheory.HermitianCauchySchwarz.main : ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : Module ℂ V] (I : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ), (∀ (x : V), (0 : ℂ) ≤ ((I : V → V →ₗ[ℂ] ℂ) x : V → ℂ) x) → ∀ (x y : V), ‖((I : V → V →ₗ[ℂ] ℂ) x : V → ℂ) y‖ ^ (2 : ℕ) ≤ Complex.re (((I : V → V →ₗ[ℂ] ℂ) x : V → ℂ) x) * Complex.re (((I : V → V →ₗ[ℂ] ℂ) y : V → ℂ) y) :=
  fun I hI x y => GlobalTheory.HermitianCauchySchwarz.cauchy_schwarz I hI x y

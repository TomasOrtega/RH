import Mathlib

open Matrix

namespace GlobalTheory.CompanionTheory.Herm

/- English proof (translation)
Take `⟨c, hc⟩ : ∃ c, c = B x w` from `⟨_, rfl⟩`. Establish `hwx : B w x = starRingEnd ℂ c` using `by rw [hc]; exact hs x w`. Establish `key : ∀ t : ℝ, 0 ≤ -2 * t * Complex.normSq c + t ^ 2 * Complex.normSq c * (B w w).re`. Introduce `t`. Establish `h` using `hp (x - ((t : ℂ) * c) • w)`.

Establish `e : B (x - ((t : ℂ) * c) • w) (x - ((t : ℂ) * c) • w) = B x x - starRingEnd ℂ ((t : ℂ) * c) * c - ((t : ℂ) * c) * starRingEnd ℂ c + ((t : ℂ) * c) * starRingEnd ℂ ((t : ℂ) * c) * B w w`. Simplify using `only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, ← hc, hwx]`. Expand and normalize the polynomial expressions, which then agree. Establish `e1 : starRingEnd ℂ ((t : ℂ) * c) * c = ((t * Complex.normSq c : ℝ) : ℂ)`. Rewrite using `[map_mul, Complex.conj_ofReal, mul_assoc, mul_comm (starRingEnd ℂ c) c, Complex.mul_conj]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ((t : ℂ) * c) * starRingEnd ℂ c = ((t * Complex.normSq c : ℝ) : ℂ)`. Rewrite using `[mul_assoc, Complex.mul_conj]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `e3 : ((t : ℂ) * c) * starRingEnd ℂ ((t : ℂ) * c) = ((t ^ 2 * Complex.normSq c : ℝ) : ℂ)`. Rewrite using `[Complex.mul_conj, Complex.normSq_mul, Complex.normSq_ofReal]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h` using `[e, e1, e2, e3]`. Simplify using `only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.re_ofReal_mul, hx] at h`. Combine the linear equalities and inequalities to obtain the conclusion. Assume the negation of the conclusion as `hne`. Establish `hc0 : c ≠ 0` using `by rw [hc]; exact hne`.

Establish `hN : 0 < Complex.normSq c` using `Complex.normSq_pos.mpr hc0`. Establish `hr : 0 ≤ (B w w).re` using `hp w`. Take `⟨r, hrdef⟩ : ∃ r, r = (B w w).re` from `⟨_, rfl⟩`. Rewrite `hr` using `[← hrdef]`. Establish `hk` using `key (1 / (r + 1))`.

Rewrite `hk` using `[← hrdef]`. Establish `hr1 : 0 < r + 1` using `by linarith`. Establish `hid : -2 * (1 / (r + 1)) * Complex.normSq c + (1 / (r + 1)) ^ 2 * Complex.normSq c * r = -(Complex.normSq c * (r + 2)) / (r + 1) ^ 2`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hk` using `[hid]`. Establish `: -(Complex.normSq c * (r + 2)) / (r + 1) ^ 2 < 0` using `div_neg_of_neg_of_pos (by nlinarith) (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem apply_eq_zero_of_isotropic {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hs : ∀ v w, B w v = starRingEnd ℂ (B v w))
    (hp : ∀ v, 0 ≤ (B v v).re) (x : V) (hx : (B x x).re = 0) (w : V) : B x w = 0 := by
  obtain ⟨c, hc⟩ : ∃ c, c = B x w := ⟨_, rfl⟩
  have hwx : B w x = starRingEnd ℂ c := by rw [hc]; exact hs x w
  have key : ∀ t : ℝ, 0 ≤ -2 * t * Complex.normSq c
      + t ^ 2 * Complex.normSq c * (B w w).re := by
    intro t
    have h := hp (x - ((t : ℂ) * c) • w)
    have e : B (x - ((t : ℂ) * c) • w) (x - ((t : ℂ) * c) • w)
        = B x x - starRingEnd ℂ ((t : ℂ) * c) * c - ((t : ℂ) * c) * starRingEnd ℂ c
          + ((t : ℂ) * c) * starRingEnd ℂ ((t : ℂ) * c) * B w w := by
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.map_smulₛₗ, smul_eq_mul, ← hc, hwx]
      ring
    have e1 : starRingEnd ℂ ((t : ℂ) * c) * c = ((t * Complex.normSq c : ℝ) : ℂ) := by
      rw [map_mul, Complex.conj_ofReal, mul_assoc, mul_comm (starRingEnd ℂ c) c,
        Complex.mul_conj]
      push_cast; ring
    have e2 : ((t : ℂ) * c) * starRingEnd ℂ c = ((t * Complex.normSq c : ℝ) : ℂ) := by
      rw [mul_assoc, Complex.mul_conj]
      push_cast; ring
    have e3 : ((t : ℂ) * c) * starRingEnd ℂ ((t : ℂ) * c)
        = ((t ^ 2 * Complex.normSq c : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_mul, Complex.normSq_ofReal]
      push_cast; ring
    rw [e, e1, e2, e3] at h
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.re_ofReal_mul, hx] at h
    linarith
  by_contra hne
  have hc0 : c ≠ 0 := by rw [hc]; exact hne
  have hN : 0 < Complex.normSq c := Complex.normSq_pos.mpr hc0
  have hr : 0 ≤ (B w w).re := hp w
  obtain ⟨r, hrdef⟩ : ∃ r, r = (B w w).re := ⟨_, rfl⟩
  rw [← hrdef] at hr
  have hk := key (1 / (r + 1))
  rw [← hrdef] at hk
  have hr1 : 0 < r + 1 := by linarith
  have hid : -2 * (1 / (r + 1)) * Complex.normSq c
      + (1 / (r + 1)) ^ 2 * Complex.normSq c * r
      = -(Complex.normSq c * (r + 2)) / (r + 1) ^ 2 := by
    field_simp
    ring
  rw [hid] at hk
  have : -(Complex.normSq c * (r + 2)) / (r + 1) ^ 2 < 0 :=
    div_neg_of_neg_of_pos (by nlinarith) (by positivity)
  linarith

end GlobalTheory.CompanionTheory.Herm

import Mathlib

namespace PI.UnitaryGroupMassFormula.UnimodLocStd

open Polynomial in
/- English proof (translation)
Establish `normForm_surj_zmod_lemma {l : ℕ} [Fact l.Prime] (A B : ZMod l) (D : ZMod l) (hOK : 4 * A = B ^ 2 + D) (hD : D ≠ 0) (v : ZMod l) (hv : v ≠ 0) : ∃ s t : ZMod l, s ^ 2 + B * s * t + A * t ^ 2 = v`. Establish `hl : l.Prime` using `Fact.out`. Break down `hl.eq_two_or_odd with rfl | hodd` into its components or cases. Use `⟨1, 0, ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ x : ZMod 2, x ≠ 0 → x = 1`.

Introduce `x hx`. Use `fin_cases x`. Conclude with `absurd rfl hx`. Both sides reduce to the same expression. Rewrite using `[h1 v hv]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hl2 : l ≠ 2` using `by omega`. Establish `h2 : (2 : ZMod l) ≠ 0` using `Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hl2)`. Establish `hcard : Fintype.card (ZMod l) % 2 = 1` using `by rw [ZMod.card]; exact hodd`. Use `open Polynomial in`.

Establish `hf : ((X : (ZMod l)[X]) ^ 2).degree = 2`. Rewrite using `[degree_X_pow]`. Both sides reduce to the same expression. Use `open Polynomial in`. Establish `hdeg : (C D * X ^ 2 : (ZMod l)[X]).degree = 2`.

Rewrite using `[degree_C_mul_X_pow 2 hD]`. Both sides reduce to the same expression. Use `open Polynomial in`. Establish `hg : (C D * X ^ 2 - C (4 * v) : (ZMod l)[X]).degree = 2`. Rewrite using `[degree_sub_C (by rw [hdeg]; decide), hdeg]`.

Take `⟨x, y, hxy⟩` from `FiniteField.exists_root_sum_quadratic hf hg hcard`. Simplify using `only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C] at hxy`. Use `set i : ZMod l := (2 : ZMod l)⁻¹ with hi_def`. Establish `hi : 2 * i = 1` using `mul_inv_cancel₀ h2`. Use `⟨(x - B * y) * i, y, ?_⟩` and prove the remaining obligations.

Establish `h4 : (4 : ZMod l) ≠ 0`. Establish `: (4 : ZMod l) = 2 * 2` using `by norm_num`. Rewrite using `[this]`. Conclude with `mul_ne_zero h2 h2`. Apply `mul_left_cancel₀ h4` to reduce the goal to its premises.

Take the linear combination `hxy + y ^ 2 * hOK + ((2 * i + 1) * (x - B * y) ^ 2 + 2 * B * y * (x - B * y)) * hi`. Use `Fact.mk hl` as an intermediate fact. Establish `: NeZero l` using `⟨hl.ne_zero⟩`. Establish `nz : ∀ z : ℤ, ¬ (l : ℤ) ∣ z → (z : ZMod l) ≠ 0` using `fun z hz h => hz ((ZMod.intCast_zmod_eq_zero_iff_dvd z l).mp h)`. Establish `hOK' : 4 * (((a : ℤ) : ZMod l) * (c : ZMod l)) = (b : ZMod l) ^ 2 + ((d : ℤ) : ZMod l)`.

Use `congrArg (Int.cast : ℤ → ZMod l) hOK` as an intermediate fact. Move the coercions through the operations in `at this ⊢`. Take the linear combination `this`. Establish `hN'` using `nz N hN`. Take `⟨s, t, hst⟩` from `normForm_surj_zmod_lemma (((a : ℤ) : ZMod l) * (c : ZMod l)) (b : ZMod l) ((d : ℤ) : ZMod l) hOK' (nz _ hld) ((Q0 : ZMod l) * (S : ZMod l) * (N : ZMod l)⁻¹) (mul_ne_zero (mul_ne_zero (nz _ hQ) (nz _ hS)) (inv_ne_zero hN'))`.

Use `⟨(s.val : ℤ), (t.val : ℤ), ?_⟩` and prove the remaining obligations. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Establish `hs : ((s.val : ℤ) : ZMod l) = s` using `by rw [Int.cast_natCast, ZMod.natCast_zmod_val]`. Establish `ht : ((t.val : ℤ) : ZMod l) = t` using `by rw [Int.cast_natCast, ZMod.natCast_zmod_val]`. Simplify using `only [Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_pow, hs, ht]`.

Establish `hst' : s ^ 2 + (b : ZMod l) * s * t + ((a : ℤ) : ZMod l) * (c : ZMod l) * t ^ 2 = (Q0 : ZMod l) * (S : ZMod l) * (N : ZMod l)⁻¹` using `hst`. Rewrite using `[hst', mul_assoc, inv_mul_cancel₀ hN', mul_one, sub_self]`.
-/
theorem rep_rep_modl {l : ℕ} (hl : l.Prime) (a : ℕ) (b c : ℤ) (d : ℕ) (hOK : 4 * (a : ℤ) * c = b ^ 2 + d)
    (hld : ¬ (l : ℤ) ∣ d) (N S Q0 : ℤ) (hN : ¬ (l : ℤ) ∣ N) (hS : ¬ (l : ℤ) ∣ S) (hQ : ¬ (l : ℤ) ∣ Q0) :
    ∃ s t : ℤ, (l : ℤ) ∣ (s ^ 2 + b * s * t + a * c * t ^ 2) * N - Q0 * S := by
  have normForm_surj_zmod_lemma {l : ℕ} [Fact l.Prime] (A B : ZMod l) (D : ZMod l)
      (hOK : 4 * A = B ^ 2 + D) (hD : D ≠ 0) (v : ZMod l) (hv : v ≠ 0) :
      ∃ s t : ZMod l, s ^ 2 + B * s * t + A * t ^ 2 = v := by
    have hl : l.Prime := Fact.out
    rcases hl.eq_two_or_odd with rfl | hodd
    · refine ⟨1, 0, ?_⟩
      have h1 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by
        intro x hx; fin_cases x
        · exact absurd rfl hx
        · rfl
      rw [h1 v hv]; ring
    · have hl2 : l ≠ 2 := by omega
      have h2 : (2 : ZMod l) ≠ 0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hl2)
      have hcard : Fintype.card (ZMod l) % 2 = 1 := by rw [ZMod.card]; exact hodd
      open Polynomial in
      have hf : ((X : (ZMod l)[X]) ^ 2).degree = 2 := by
        rw [degree_X_pow]; rfl
      open Polynomial in
      have hdeg : (C D * X ^ 2 : (ZMod l)[X]).degree = 2 := by
        rw [degree_C_mul_X_pow 2 hD]; rfl
      open Polynomial in
      have hg : (C D * X ^ 2 - C (4 * v) : (ZMod l)[X]).degree = 2 := by
        rw [degree_sub_C (by rw [hdeg]; decide), hdeg]
      obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg hcard
      simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_C] at hxy
      set i : ZMod l := (2 : ZMod l)⁻¹ with hi_def
      have hi : 2 * i = 1 := mul_inv_cancel₀ h2
      refine ⟨(x - B * y) * i, y, ?_⟩
      have h4 : (4 : ZMod l) ≠ 0 := by
        have : (4 : ZMod l) = 2 * 2 := by norm_num
        rw [this]; exact mul_ne_zero h2 h2
      apply mul_left_cancel₀ h4
      linear_combination hxy + y ^ 2 * hOK + ((2 * i + 1) * (x - B * y) ^ 2 + 2 * B * y * (x - B * y)) * hi
  have := Fact.mk hl
  have : NeZero l := ⟨hl.ne_zero⟩
  have nz : ∀ z : ℤ, ¬ (l : ℤ) ∣ z → (z : ZMod l) ≠ 0 := fun z hz h =>
    hz ((ZMod.intCast_zmod_eq_zero_iff_dvd z l).mp h)
  have hOK' : 4 * (((a : ℤ) : ZMod l) * (c : ZMod l)) = (b : ZMod l) ^ 2 + ((d : ℤ) : ZMod l) := by
    have := congrArg (Int.cast : ℤ → ZMod l) hOK
    push_cast at this ⊢
    linear_combination this
  have hN' := nz N hN
  obtain ⟨s, t, hst⟩ := normForm_surj_zmod_lemma (((a : ℤ) : ZMod l) * (c : ZMod l)) (b : ZMod l)
    ((d : ℤ) : ZMod l) hOK' (nz _ hld) ((Q0 : ZMod l) * (S : ZMod l) * (N : ZMod l)⁻¹)
    (mul_ne_zero (mul_ne_zero (nz _ hQ) (nz _ hS)) (inv_ne_zero hN'))
  refine ⟨(s.val : ℤ), (t.val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hs : ((s.val : ℤ) : ZMod l) = s := by rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have ht : ((t.val : ℤ) : ZMod l) = t := by rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_pow, hs, ht]
  have hst' : s ^ 2 + (b : ZMod l) * s * t + ((a : ℤ) : ZMod l) * (c : ZMod l) * t ^ 2
      = (Q0 : ZMod l) * (S : ZMod l) * (N : ZMod l)⁻¹ := hst
  rw [hst', mul_assoc, inv_mul_cancel₀ hN', mul_one, sub_self]

end PI.UnitaryGroupMassFormula.UnimodLocStd

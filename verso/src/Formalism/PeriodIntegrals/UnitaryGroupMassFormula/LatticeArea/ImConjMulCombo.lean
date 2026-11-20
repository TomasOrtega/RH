import Mathlib
import Formalism.PeriodIntegrals.AreaLat

namespace PI.AreaLatWork

open PI

/- English proof (translation)
Simplify using `only [zsmul_eq_mul, map_add, map_mul, map_intCast, Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.intCast_re, Complex.intCast_im, Complex.conj_re, Complex.conj_im]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma im_conj_mul_combo (w₁ w₂ : ℂ) (m n m' n' : ℤ) :
    ((starRingEnd ℂ) (m • w₁ + n • w₂) * (m' • w₁ + n' • w₂)).im
      = ((m * n' - n * m' : ℤ) : ℝ) * ((starRingEnd ℂ) w₁ * w₂).im := by
  simp only [zsmul_eq_mul, map_add, map_mul, map_intCast, Complex.mul_im, Complex.mul_re,
    Complex.add_re, Complex.add_im, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im]
  push_cast
  ring

/- English proof (translation)
Introduce `a ha b hb`. Take `⟨m, n, rfl⟩` from `(AddSubgroup.mem_closure_pair (x := w₁) (y := w₂)).mp ha`. Take `⟨m', n', rfl⟩` from `(AddSubgroup.mem_closure_pair (x := w₁) (y := w₂)).mp hb`. Conclude with `⟨m * n' - n * m', im_conj_mul_combo w₁ w₂ m n m' n'⟩`.
-/
lemma im_integral (w₁ w₂ : ℂ) :
    ∀ a ∈ lat2 w₁ w₂, ∀ b ∈ lat2 w₁ w₂,
      ∃ n : ℤ, ((starRingEnd ℂ) a * b).im = n * ((starRingEnd ℂ) w₁ * w₂).im := by
  intro a ha b hb
  obtain ⟨m, n, rfl⟩ := (AddSubgroup.mem_closure_pair (x := w₁) (y := w₂)).mp ha
  obtain ⟨m', n', rfl⟩ := (AddSubgroup.mem_closure_pair (x := w₁) (y := w₂)).mp hb
  exact ⟨m * n' - n * m', im_conj_mul_combo w₁ w₂ m n m' n'⟩

/- English proof (translation)
Introduce `w₁ w₂ hne`. Use `⟨?_, im_integral w₁ w₂⟩` and prove the remaining obligations. Unfold `PI.area`. Apply `IsLeast.csInf_eq` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion.

Use `⟨abs_pos.mpr hne, w₁, ?_, w₂, ?_, rfl⟩` and prove the remaining obligations. Conclude with `AddSubgroup.subset_closure (Set.mem_insert _ _)`. Conclude with `AddSubgroup.subset_closure (Set.mem_insert_of_mem _ rfl)`. Introduce and unpack `a ⟨ha, x, hx, y, hy, rfl⟩`. Take `⟨n, hn⟩` from `im_integral w₁ w₂ x hx y hy`.

Rewrite `ha`, the goal using `[hn, abs_mul]`. Establish `hn0 : (n : ℝ) ≠ 0`. Introduce `h0`. Rewrite `ha` using `[h0, abs_zero, zero_mul]`. Conclude with `lt_irrefl _ ha`.

Establish `hn1 : (1 : ℝ) ≤ |(n : ℝ)|`. Rewrite using `[← Int.cast_abs]`. Conclude with `Int.one_le_abs (by exact_mod_cast hn0)` after adjusting the coercions. Establish `h2` using `mul_le_mul_of_nonneg_right hn1 (abs_nonneg (((starRingEnd ℂ) w₁ * w₂).im))`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem areaLat : PI.AreaLat := by
  intro w₁ w₂ hne
  refine ⟨?_, im_integral w₁ w₂⟩
  unfold PI.area
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨abs_pos.mpr hne, w₁, ?_, w₂, ?_, rfl⟩
    · exact AddSubgroup.subset_closure (Set.mem_insert _ _)
    · exact AddSubgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  · rintro a ⟨ha, x, hx, y, hy, rfl⟩
    obtain ⟨n, hn⟩ := im_integral w₁ w₂ x hx y hy
    rw [hn, abs_mul] at ha ⊢
    have hn0 : (n : ℝ) ≠ 0 := by
      intro h0
      rw [h0, abs_zero, zero_mul] at ha
      exact lt_irrefl _ ha
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (by exact_mod_cast hn0)
    have h2 := mul_le_mul_of_nonneg_right hn1 (abs_nonneg (((starRingEnd ℂ) w₁ * w₂).im))
    linarith

end PI.AreaLatWork

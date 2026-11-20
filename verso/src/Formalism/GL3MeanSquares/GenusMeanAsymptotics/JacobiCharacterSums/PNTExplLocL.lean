import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplLF
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplLoc

open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

/- English proof (translation)
Simplify using `only [add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im, mul_zero, mul_one, sub_self]`. Establish `: ((101 / 100 : ℂ)).re = 101 / 100`. Establish `h : (101 / 100 : ℂ) = ((101 / 100 : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[h, ofReal_re]`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem ex_centre_re (t : ℝ) : ((101 / 100 : ℂ) + t * I).re = 101 / 100 := by
  simp only [add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im, mul_zero, mul_one, sub_self]
  have : ((101 / 100 : ℂ)).re = 101 / 100 := by
    have h : (101 / 100 : ℂ) = ((101 / 100 : ℝ) : ℂ) := by push_cast; ring
    rw [h, ofReal_re]
  rw [this]; ring

/- English proof (translation)
Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Establish `h1 : ‖(101 / 100 : ℂ)‖ = 101 / 100`. Establish `h : (101 / 100 : ℂ) = ((101 / 100 : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]`. Establish `h2 : ‖(t : ℂ) * I‖ = |t|`.

Rewrite using `[norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]`. Rewrite using `[h1, h2]`.
-/
theorem ex_centre_norm (t : ℝ) : ‖(101 / 100 : ℂ) + t * I‖ ≤ 101 / 100 + |t| := by
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖(101 / 100 : ℂ)‖ = 101 / 100 := by
    have h : (101 / 100 : ℂ) = ((101 / 100 : ℝ) : ℂ) := by push_cast; ring
    rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have h2 : ‖(t : ℂ) * I‖ = |t| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, h2]

/- English proof (translation)
Establish `hre` using `ex_centre_re t`. Establish `h` using `exLF_lower χ ((101 / 100 : ℂ) + t * I) (by rw [hre]; norm_num)`. Rewrite `h` using `[hre]`. Establish `h1 : (1 / 100 : ℝ) ≤ ‖(101 / 100 : ℂ) + t * I - 1‖`. Establish `h2` using `Complex.abs_re_le_norm ((101 / 100 : ℂ) + t * I - 1)`.

Rewrite `h2` using `[sub_re, hre, one_re]`. Rewrite `h2` using `[abs_of_pos (by norm_num)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : (1 / 100 : ℝ) ≤ min 1 ‖(101 / 100 : ℂ) + t * I - 1‖` using `le_min (by norm_num) h1`. Establish `h4 : (1 / 100 : ℝ) * ((101 / 100 - 1) / (101 / 100)) ≤ min 1 ‖(101 / 100 : ℂ) + t * I - 1‖ * ((101 / 100 - 1) / (101 / 100))` using `mul_le_mul_of_nonneg_right h3 (by norm_num)`.

Use `le_trans ?_ (h4.trans h)` and prove the remaining obligations. Evaluate the numerical expressions.
-/
theorem ex_centre_lower {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (t : ℝ) :
    1 / 10100 ≤ ‖exLF χ ((101 / 100 : ℂ) + t * I)‖ := by
  have hre := ex_centre_re t
  have h := exLF_lower χ ((101 / 100 : ℂ) + t * I) (by rw [hre]; norm_num)
  rw [hre] at h
  have h1 : (1 / 100 : ℝ) ≤ ‖(101 / 100 : ℂ) + t * I - 1‖ := by
    have h2 := Complex.abs_re_le_norm ((101 / 100 : ℂ) + t * I - 1)
    rw [sub_re, hre, one_re] at h2
    rw [abs_of_pos (by norm_num)] at h2
    linarith
  have h3 : (1 / 100 : ℝ) ≤ min 1 ‖(101 / 100 : ℂ) + t * I - 1‖ := le_min (by norm_num) h1
  have h4 : (1 / 100 : ℝ) * ((101 / 100 - 1) / (101 / 100)) ≤
      min 1 ‖(101 / 100 : ℂ) + t * I - 1‖ * ((101 / 100 - 1) / (101 / 100)) :=
    mul_le_mul_of_nonneg_right h3 (by norm_num)
  refine le_trans ?_ (h4.trans h)
  norm_num

/- English proof (translation)
Establish `hM3 : (3 : ℝ) ≤ M` using `by exact_mod_cast hM`. Establish `ht : 0 ≤ |t|` using `abs_nonneg t`. Establish `hB1 : 1 ≤ C0 * M * (|t| + 3) ^ 2 * 10100`. Establish `h1 : 1 ≤ C0 * M` using `by nlinarith`. Establish `h2 : 1 ≤ (|t| + 3) ^ 2` using `by nlinarith`.

Establish `h3 : 1 ≤ C0 * M * (|t| + 3) ^ 2` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨hB1, Real.log_nonneg hB1, ?_⟩` and prove the remaining obligations. Use `set X : ℝ := (M : ℝ) * (|t| + 2) with hX`. Establish `hX6 : 6 ≤ X` using `by rw [hX]; nlinarith`.

Establish `hX0 : 0 < X` using `by linarith`. Establish `hMX : (M : ℝ) ≤ X` using `by rw [hX]; nlinarith`. Establish `htX : |t| + 3 ≤ X` using `by rw [hX]; nlinarith`. Establish `hlogX : 1 ≤ Real.log X`. Rewrite using `[Real.le_log_iff_exp_le hX0]`.

Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hK : 1 ≤ C0 * 10100` using `by linarith`. Establish `hK0 : 0 ≤ Real.log (C0 * 10100)` using `Real.log_nonneg hK`. Establish `hle : C0 * M * (|t| + 3) ^ 2 * 10100 ≤ C0 * 10100 * X ^ 3`.

Establish `h1 : (|t| + 3) ^ 2 ≤ X ^ 2` using `by gcongr`. Establish `h2 : (M : ℝ) * (|t| + 3) ^ 2 ≤ X * X ^ 2`. Apply `mul_le_mul hMX h1 (by positivity) hX0.le` to reduce the goal to its premises. Establish `h3 : C0 * 10100 * ((M : ℝ) * (|t| + 3) ^ 2) ≤ C0 * 10100 * (X * X ^ 2)` using `mul_le_mul_of_nonneg_left h2 (by linarith)`. Combine the equalities or inequalities in the displayed calculation.

Establish `h5 : Real.log (C0 * M * (|t| + 3) ^ 2 * 10100) ≤ Real.log (C0 * 10100 * X ^ 3)` using `Real.log_le_log (by linarith) hle`. Establish `h6 : Real.log (C0 * 10100 * X ^ 3) = Real.log (C0 * 10100) + 3 * Real.log X`. Rewrite using `[Real.log_mul (by linarith) (by positivity), Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h5` using `[h6]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem ex_log_bound (C0 : ℝ) (hC0 : 1 ≤ C0) (M : ℕ) (hM : 3 ≤ M) (t : ℝ) :
    1 ≤ C0 * M * (|t| + 3) ^ 2 * 10100 ∧
    0 ≤ Real.log (C0 * M * (|t| + 3) ^ 2 * 10100) ∧
    Real.log (C0 * M * (|t| + 3) ^ 2 * 10100) ≤
      (Real.log (C0 * 10100) + 3) * Real.log ((M : ℝ) * (|t| + 2)) := by
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have ht : 0 ≤ |t| := abs_nonneg t
  have hB1 : 1 ≤ C0 * M * (|t| + 3) ^ 2 * 10100 := by
    have h1 : 1 ≤ C0 * M := by nlinarith
    have h2 : 1 ≤ (|t| + 3) ^ 2 := by nlinarith
    have h3 : 1 ≤ C0 * M * (|t| + 3) ^ 2 := by nlinarith
    linarith
  refine ⟨hB1, Real.log_nonneg hB1, ?_⟩
  set X : ℝ := (M : ℝ) * (|t| + 2) with hX
  have hX6 : 6 ≤ X := by rw [hX]; nlinarith
  have hX0 : 0 < X := by linarith
  have hMX : (M : ℝ) ≤ X := by rw [hX]; nlinarith
  have htX : |t| + 3 ≤ X := by rw [hX]; nlinarith
  have hlogX : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    have := Real.exp_one_lt_d9
    linarith
  have hK : 1 ≤ C0 * 10100 := by linarith
  have hK0 : 0 ≤ Real.log (C0 * 10100) := Real.log_nonneg hK
  have hle : C0 * M * (|t| + 3) ^ 2 * 10100 ≤ C0 * 10100 * X ^ 3 := by
    have h1 : (|t| + 3) ^ 2 ≤ X ^ 2 := by gcongr
    have h2 : (M : ℝ) * (|t| + 3) ^ 2 ≤ X * X ^ 2 := by
      apply mul_le_mul hMX h1 (by positivity) hX0.le
    have h3 : C0 * 10100 * ((M : ℝ) * (|t| + 3) ^ 2) ≤ C0 * 10100 * (X * X ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    calc C0 * M * (|t| + 3) ^ 2 * 10100 = C0 * 10100 * ((M : ℝ) * (|t| + 3) ^ 2) := by ring
      _ ≤ C0 * 10100 * (X * X ^ 2) := h3
      _ = C0 * 10100 * X ^ 3 := by ring
  have h5 : Real.log (C0 * M * (|t| + 3) ^ 2 * 10100) ≤ Real.log (C0 * 10100 * X ^ 3) :=
    Real.log_le_log (by linarith) hle
  have h6 : Real.log (C0 * 10100 * X ^ 3) = Real.log (C0 * 10100) + 3 * Real.log X := by
    rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]
    push_cast; ring
  rw [h6] at h5
  nlinarith

/- English proof (translation)
Take `⟨C0, hC0, hG⟩` from `exLF_growth`. Establish `hK0 : 0 ≤ Real.log (C0 * 10100)` using `Real.log_nonneg (by linarith)`. Use `⟨180 * (Real.log (C0 * 10100) + 3), by linarith, ?_⟩` and prove the remaining obligations. Introduce `M _ χ t hM`. Take `⟨hB1, hB0, hBlog⟩` from `ex_log_bound C0 hC0 M hM t`.

Use `set B : ℝ := C0 * M * (|t| + 3) ^ 2 * 10100 with hB`. Use `set z₀ : ℂ := (101 / 100 : ℂ) + t * I with hz₀`. Establish `hlow : 1 / 10100 ≤ ‖exLF χ z₀‖` using `ex_centre_lower χ t`. Establish `hne : exLF χ z₀ ≠ 0`. Introduce `h`.

Rewrite `hlow` using `[h, norm_zero]`. Evaluate the numerical expressions using `at hlow`. Establish `hM0 : (0 : ℝ) ≤ M` using `Nat.cast_nonneg M`. Establish `hbound : ∀ z ∈ Metric.closedBall z₀ (2 / 5), ‖exLF χ z‖ ≤ B * ‖exLF χ z₀‖`. Introduce `z hz`.

Rewrite `hz` using `[Metric.mem_closedBall, dist_eq_norm]`. Establish `hre : 1 / 2 ≤ z.re`. Establish `h1` using `Complex.abs_re_le_norm (z - z₀)`. Rewrite `h1` using `[sub_re, hz₀, ex_centre_re t]`. Establish `h2` using `(abs_le.1 (h1.trans hz)).1`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn : ‖z‖ ≤ |t| + 2`. Establish `h1 : ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖`. Use `norm_add_le (z - z₀) z₀` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.

Establish `h2` using `ex_centre_norm t`. Rewrite `h2` using `[← hz₀]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : (1 + ‖z‖) ^ 2 ≤ (|t| + 3) ^ 2`. Establish `: 0 ≤ ‖z‖` using `norm_nonneg z`.

Conclude with `pow_le_pow_left₀ (by linarith) (by linarith) 2`. Establish `h4 : C0 * M * (1 + ‖z‖) ^ 2 ≤ C0 * M * (|t| + 3) ^ 2` using `mul_le_mul_of_nonneg_left h3 (mul_nonneg (by linarith) hM0)`. Establish `h5 : B * (1 / 10100) ≤ B * ‖exLF χ z₀‖` using `mul_le_mul_of_nonneg_left hlow (by linarith)`. Establish `h6 : B * (1 / 10100) = C0 * M * (|t| + 3) ^ 2` using `by rw [hB]; ring`. Combine the linear relations using `[hG M χ z hre]`.

Take `⟨Z, hZ1, -, hZ3, hZ4⟩` from `ex_landau_ord (exLF χ) z₀ (2 / 5) B (by norm_num) hB1 (exLF_differentiable χ).differentiableOn hne hbound`. Establish `e3 : (2 / 5 : ℝ) / 3 = 2 / 15` using `by norm_num`. Establish `e6 : (2 / 5 : ℝ) / 6 = 1 / 15` using `by norm_num`. Rewrite `hZ1` using `[e3]`. Rewrite `hZ4` using `[e6]`.

Use `⟨Z, hZ1, ?_, ?_⟩` and prove the remaining obligations. Establish `h2 : Real.log B / Real.log 2 ≤ 180 * Real.log B`. Establish `hl2 : (1 / 2 : ℝ) ≤ Real.log 2` using `by have := Real.log_two_gt_d9; linarith`. Rewrite using `[div_le_iff₀ (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h3 : ((∑ ρ ∈ Z, exOrd χ ρ : ℕ) : ℝ) ≤ Real.log B / Real.log 2` using `hZ3`. Combine the equalities or inequalities in the displayed calculation. Introduce `s hs hs0`. Establish `h1 : ‖deriv (exLF χ) s / exLF χ s - ∑ ρ ∈ Z, (exOrd χ ρ : ℂ) / (s - ρ)‖ ≤ 72 * Real.log B / (2 / 5)` using `hZ4 s hs hs0`. Establish `h2 : 72 * Real.log B / (2 / 5) = 180 * Real.log B` using `by ring`.

Rewrite `h1` using `[h2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ex_local : ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (t : ℝ), 3 ≤ M →
    ∃ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall ((101 / 100 : ℂ) + t * I) (2 / 15) ∧ exLF χ ρ = 0)) ∧
      ((∑ ρ ∈ Z, exOrd χ ρ : ℕ) : ℝ) ≤ C * Real.log ((M : ℝ) * (|t| + 2)) ∧
      ∀ s ∈ Metric.closedBall ((101 / 100 : ℂ) + t * I) (1 / 15), exLF χ s ≠ 0 →
        ‖deriv (exLF χ) s / exLF χ s - ∑ ρ ∈ Z, (exOrd χ ρ : ℂ) / (s - ρ)‖ ≤
          C * Real.log ((M : ℝ) * (|t| + 2)) := by
  obtain ⟨C0, hC0, hG⟩ := exLF_growth
  have hK0 : 0 ≤ Real.log (C0 * 10100) := Real.log_nonneg (by linarith)
  refine ⟨180 * (Real.log (C0 * 10100) + 3), by linarith, ?_⟩
  intro M _ χ t hM
  obtain ⟨hB1, hB0, hBlog⟩ := ex_log_bound C0 hC0 M hM t
  set B : ℝ := C0 * M * (|t| + 3) ^ 2 * 10100 with hB
  set z₀ : ℂ := (101 / 100 : ℂ) + t * I with hz₀
  have hlow : 1 / 10100 ≤ ‖exLF χ z₀‖ := ex_centre_lower χ t
  have hne : exLF χ z₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hlow; norm_num at hlow
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hbound : ∀ z ∈ Metric.closedBall z₀ (2 / 5), ‖exLF χ z‖ ≤ B * ‖exLF χ z₀‖ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre : 1 / 2 ≤ z.re := by
      have h1 := Complex.abs_re_le_norm (z - z₀)
      rw [sub_re, hz₀, ex_centre_re t] at h1
      have h2 := (abs_le.1 (h1.trans hz)).1
      linarith
    have hn : ‖z‖ ≤ |t| + 2 := by
      have h1 : ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ := by
        have := norm_add_le (z - z₀) z₀
        rwa [sub_add_cancel] at this
      have h2 := ex_centre_norm t
      rw [← hz₀] at h2
      linarith
    have h3 : (1 + ‖z‖) ^ 2 ≤ (|t| + 3) ^ 2 := by
      have : 0 ≤ ‖z‖ := norm_nonneg z
      exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h4 : C0 * M * (1 + ‖z‖) ^ 2 ≤ C0 * M * (|t| + 3) ^ 2 :=
      mul_le_mul_of_nonneg_left h3 (mul_nonneg (by linarith) hM0)
    have h5 : B * (1 / 10100) ≤ B * ‖exLF χ z₀‖ := mul_le_mul_of_nonneg_left hlow (by linarith)
    have h6 : B * (1 / 10100) = C0 * M * (|t| + 3) ^ 2 := by rw [hB]; ring
    linarith [hG M χ z hre]
  obtain ⟨Z, hZ1, -, hZ3, hZ4⟩ := ex_landau_ord (exLF χ) z₀ (2 / 5) B (by norm_num) hB1
    (exLF_differentiable χ).differentiableOn hne hbound
  have e3 : (2 / 5 : ℝ) / 3 = 2 / 15 := by norm_num
  have e6 : (2 / 5 : ℝ) / 6 = 1 / 15 := by norm_num
  rw [e3] at hZ1
  rw [e6] at hZ4
  refine ⟨Z, hZ1, ?_, ?_⟩
  · have h2 : Real.log B / Real.log 2 ≤ 180 * Real.log B := by
      have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have h3 : ((∑ ρ ∈ Z, exOrd χ ρ : ℕ) : ℝ) ≤ Real.log B / Real.log 2 := hZ3
    calc ((∑ ρ ∈ Z, exOrd χ ρ : ℕ) : ℝ) ≤ 180 * Real.log B := h3.trans h2
      _ ≤ 180 * (Real.log (C0 * 10100) + 3) * Real.log ((M : ℝ) * (|t| + 2)) := by linarith
  · intro s hs hs0
    have h1 : ‖deriv (exLF χ) s / exLF χ s - ∑ ρ ∈ Z, (exOrd χ ρ : ℂ) / (s - ρ)‖ ≤
        72 * Real.log B / (2 / 5) := hZ4 s hs hs0
    have h2 : 72 * Real.log B / (2 / 5) = 180 * Real.log B := by ring
    rw [h2] at h1
    linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions

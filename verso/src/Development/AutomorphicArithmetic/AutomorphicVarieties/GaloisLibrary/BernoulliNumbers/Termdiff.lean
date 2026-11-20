import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BTaylor2

open Finset UpperTheory.V.Bern

/- English proof (translation)
Rewrite using `[abs_of_pos ha]`. Establish `p1 : 0 ≤ 1 / a ^ (3 / 2 : ℝ)` using `by positivity`. Establish `p2 : 0 ≤ 1 / a ^ (5 : ℝ)` using `by positivity`. Break down `le_or_gt 1 a with h | h` into its components or cases. Establish `h' : a ^ e ≤ a ^ (-(3 / 2) : ℝ)` using `Real.rpow_le_rpow_of_exponent_le h h2`.

Rewrite `h'` using `[Real.rpow_neg ha.le, ← one_div]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h' : a ^ e ≤ a ^ (-5 : ℝ)` using `Real.rpow_le_rpow_of_exponent_ge ha h.le h1`. Rewrite `h'` using `[Real.rpow_neg ha.le, ← one_div]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem termdiff_rpow_le {a e : ℝ} (ha : 0 < a) (h1 : -5 ≤ e) (h2 : e ≤ -(3 / 2)) :
    a ^ e ≤ 1 / |a| ^ (3 / 2 : ℝ) + 1 / |a| ^ (5 : ℝ) := by
  rw [abs_of_pos ha]
  have p1 : 0 ≤ 1 / a ^ (3 / 2 : ℝ) := by positivity
  have p2 : 0 ≤ 1 / a ^ (5 : ℝ) := by positivity
  rcases le_or_gt 1 a with h | h
  · have h' : a ^ e ≤ a ^ (-(3 / 2) : ℝ) := Real.rpow_le_rpow_of_exponent_le h h2
    rw [Real.rpow_neg ha.le, ← one_div] at h'
    linarith
  · have h' : a ^ e ≤ a ^ (-5 : ℝ) := Real.rpow_le_rpow_of_exponent_ge ha h.le h1
    rw [Real.rpow_neg ha.le, ← one_div] at h'
    linarith

/- English proof (translation)
Conclude with `Differentiable.const_cpow differentiable_id.neg (Or.inl (by exact_mod_cast ha.ne'))`.
-/
private theorem termdiff_cpow {a : ℝ} (ha : 0 < a) : Differentiable ℂ (fun s : ℂ => (a : ℂ) ^ (-s)) := by
  exact Differentiable.const_cpow differentiable_id.neg (Or.inl (by exact_mod_cast ha.ne'))

/- English proof (translation)
Introduce `x hx0 hx1`. Establish `hU : IsOpen ({s : ℂ | -1 / 2 < s.re} ∩ Metric.ball 0 3)` using `(isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball`. Use `Complex.differentiableOn_tsum_of_summable_norm (u := fun n : ℕ => 24 * (1 / |(n : ℝ) + x| ^ (3 / 2 : ℝ) + 1 / |(n : ℝ) + x| ^ (5 : ℝ))) ?_ ?_ hU ?_` and prove the remaining obligations. Conclude with `(((Real.summable_one_div_nat_add_rpow x (3 / 2)).2 (by norm_num)).add ((Real.summable_one_div_nat_add_rpow x 5).2 (by norm_num))).mul_left 24`. Introduce `n`.

Establish `hb : ∀ b : ℝ, 0 < b → Differentiable ℂ (fun s : ℂ => (b : ℂ) ^ (-s))` using `fun b hb => termdiff_cpow hb`. Establish `h1 : (0 : ℝ) < (n : ℝ) + x` using `by positivity`. Establish `h2 : (0 : ℝ) < (n : ℝ) + 1` using `by positivity`. Establish `h3 : (0 : ℝ) < (n : ℝ) + 2` using `by positivity`. Conclude with `(((hb _ h1).sub (hb _ h2)).sub ((differentiable_const _).mul ((hb _ h2).sub (hb _ h3)))).differentiableOn`.

Introduce `n s hs`. Take `⟨hre, hball⟩` from `hs`. Simplify using `only [Set.mem_setOf_eq] at hre`. Rewrite `hball` using `[mem_ball_zero_iff]`. Establish `ha : (0 : ℝ) < (n : ℝ) + x` using `by positivity`.

Establish `hre2 : -2 ≤ s.re` using `by linarith`. Establish `hR1` using `b_taylor2 s ((n : ℝ) + x) ((n : ℝ) + 1) ((n : ℝ) + x) ha (by linarith) le_rfl hre2`. Establish `hR2` using `b_taylor2 s ((n : ℝ) + x) ((n : ℝ) + 1) ((n : ℝ) + 2) ha (by linarith) (by linarith) hre2`. Establish `hA` using `termdiff_rpow_le ha (e := -s.re - 2) (by linarith [Complex.re_le_norm s]) (by linarith)`. Establish `hA0 : 0 ≤ ((n : ℝ) + x) ^ (-s.re - 2)` using `Real.rpow_nonneg ha.le _`.

Establish `hs1 : ‖s + 1‖ ≤ 4`. Use `norm_add_le s 1` as an intermediate fact. Rewrite `this` using `[norm_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hP : ‖s‖ * ‖s + 1‖ ≤ 3 * 4` using `mul_le_mul hball.le hs1 (norm_nonneg _) (by norm_num)`.

Use `set B := 1 / |(n : ℝ) + x| ^ (3 / 2 : ℝ) + 1 / |(n : ℝ) + x| ^ (5 : ℝ) with hB`. Establish `hB0 : 0 ≤ B` using `hA0.trans hA`. Establish `hsq1 : ((n : ℝ) + x - ((n : ℝ) + 1)) ^ 2 ≤ 1` using `by nlinarith`. Establish `hsq2 : ((n : ℝ) + 2 - ((n : ℝ) + 1)) ^ 2 ≤ 1` using `by nlinarith`. Establish `hR1'` using `hR1.trans (mul_le_mul (mul_le_mul hP hA hA0 (by norm_num)) hsq1 (sq_nonneg _) (by positivity))`.

Establish `hR2'` using `hR2.trans (mul_le_mul (mul_le_mul hP hA hA0 (by norm_num)) hsq2 (sq_nonneg _) (by positivity))`. Establish `hnx : ‖(1 : ℂ) - (x : ℂ)‖ ≤ 1`. Rewrite using `[← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]`. Apply the tactic sequence `constructor <;> linarith`. Combine the equalities or inequalities in the displayed calculation.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ 3 * 4 * B * 1 + 1 * (3 * 4 * B * 1) := (norm_add_le _ _).trans (by`. Rewrite using `[norm_mul]`.

Conclude with `add_le_add hR1' (mul_le_mul hnx hR2' (norm_nonneg _) zero_le_one))`. Use `_ = 24 * B := by ring`.
-/
theorem UpperTheory.V.Bern.b_termdiff :
    ∀ (x : ℝ), 0 < x → x ≤ 1 → DifferentiableOn ℂ (fun s : ℂ => ∑' n : ℕ, ((((n : ℝ) + x : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (1 - (x : ℂ)) * ((((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 2 : ℝ) : ℂ) ^ (-s)))) ({s : ℂ | -1 / 2 < s.re} ∩ Metric.ball 0 3) := by
  intro x hx0 hx1
  have hU : IsOpen ({s : ℂ | -1 / 2 < s.re} ∩ Metric.ball 0 3) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  refine Complex.differentiableOn_tsum_of_summable_norm
    (u := fun n : ℕ => 24 * (1 / |(n : ℝ) + x| ^ (3 / 2 : ℝ) + 1 / |(n : ℝ) + x| ^ (5 : ℝ)))
    ?_ ?_ hU ?_
  · exact (((Real.summable_one_div_nat_add_rpow x (3 / 2)).2 (by norm_num)).add
      ((Real.summable_one_div_nat_add_rpow x 5).2 (by norm_num))).mul_left 24
  · intro n
    have hb : ∀ b : ℝ, 0 < b → Differentiable ℂ (fun s : ℂ => (b : ℂ) ^ (-s)) :=
      fun b hb => termdiff_cpow hb
    have h1 : (0 : ℝ) < (n : ℝ) + x := by positivity
    have h2 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h3 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    exact (((hb _ h1).sub (hb _ h2)).sub
      ((differentiable_const _).mul ((hb _ h2).sub (hb _ h3)))).differentiableOn
  · intro n s hs
    obtain ⟨hre, hball⟩ := hs
    simp only [Set.mem_setOf_eq] at hre
    rw [mem_ball_zero_iff] at hball
    have ha : (0 : ℝ) < (n : ℝ) + x := by positivity
    have hre2 : -2 ≤ s.re := by linarith
    have hR1 := b_taylor2 s ((n : ℝ) + x) ((n : ℝ) + 1) ((n : ℝ) + x) ha (by linarith) le_rfl hre2
    have hR2 := b_taylor2 s ((n : ℝ) + x) ((n : ℝ) + 1) ((n : ℝ) + 2) ha (by linarith) (by linarith) hre2
    have hA := termdiff_rpow_le ha (e := -s.re - 2)
      (by linarith [Complex.re_le_norm s]) (by linarith)
    have hA0 : 0 ≤ ((n : ℝ) + x) ^ (-s.re - 2) := Real.rpow_nonneg ha.le _
    have hs1 : ‖s + 1‖ ≤ 4 := by
      have := norm_add_le s 1
      rw [norm_one] at this
      linarith
    have hP : ‖s‖ * ‖s + 1‖ ≤ 3 * 4 := mul_le_mul hball.le hs1 (norm_nonneg _) (by norm_num)
    set B := 1 / |(n : ℝ) + x| ^ (3 / 2 : ℝ) + 1 / |(n : ℝ) + x| ^ (5 : ℝ) with hB
    have hB0 : 0 ≤ B := hA0.trans hA
    have hsq1 : ((n : ℝ) + x - ((n : ℝ) + 1)) ^ 2 ≤ 1 := by nlinarith
    have hsq2 : ((n : ℝ) + 2 - ((n : ℝ) + 1)) ^ 2 ≤ 1 := by nlinarith
    have hR1' := hR1.trans (mul_le_mul (mul_le_mul hP hA hA0 (by norm_num)) hsq1 (sq_nonneg _) (by positivity))
    have hR2' := hR2.trans (mul_le_mul (mul_le_mul hP hA hA0 (by norm_num)) hsq2 (sq_nonneg _) (by positivity))
    have hnx : ‖(1 : ℂ) - (x : ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    calc _ = ‖((((n : ℝ) + x : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
              + s * ((((n : ℝ) + x : ℝ) : ℂ) - (((n : ℝ) + 1 : ℝ) : ℂ)) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s - 1))
            + (1 - (x : ℂ)) * ((((n : ℝ) + 2 : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
              + s * ((((n : ℝ) + 2 : ℝ) : ℂ) - (((n : ℝ) + 1 : ℝ) : ℂ)) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s - 1))‖ := by
          congr 1
          push_cast
          ring
      _ ≤ 3 * 4 * B * 1 + 1 * (3 * 4 * B * 1) :=
          (norm_add_le _ _).trans (by
            rw [norm_mul]
            exact add_le_add hR1' (mul_le_mul hnx hR2' (norm_nonneg _) zero_le_one))
      _ = 24 * B := by ring

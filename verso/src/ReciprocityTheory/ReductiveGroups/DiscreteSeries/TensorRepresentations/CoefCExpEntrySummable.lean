import Mathlib

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

/- English proof (translation)
Proceed by induction on `j generalizing c d with`. Consider the case `zero`. Simplify using `only [pow_zero]`. Distinguish the cases in `h : c = d`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne h]`. Consider the case `succ j ih`. Rewrite using `[pow_succ, Matrix.mul_apply, pow_succ]`. Establish `hN0 : 0 ≤ ∑ a, ∑ b, ‖B a b‖` using `by positivity`.

Establish `hN : ∑ e, ‖B e d‖ ≤ ∑ a, ∑ b, ‖B a b‖`. Use `Finset.sum_le_sum fun e _ => ?_` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun b => ‖B e b‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ d)`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun e _ => ?_` and prove the remaining obligations.

Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (ih c e) (norm_nonneg _)`. Use `_ = (∑ a, ∑ b, ‖B a b‖) ^ j * ∑ e, ‖B e d‖ := by rw [Finset.mul_sum]`. Use `_ ≤ (∑ a, ∑ b, ‖B a b‖) ^ j * ∑ a, ∑ b, ‖B a b‖ := mul_le_mul_of_nonneg_left hN (pow_nonneg hN0 _)`.
-/
theorem coefC_pow_entry_le (B : Matrix (Fin n) (Fin n) ℂ) (j : ℕ) (c d : Fin n) :
    ‖(B ^ j) c d‖ ≤ (∑ a, ∑ b, ‖B a b‖) ^ j := by
  induction j generalizing c d with
  | zero =>
    simp only [pow_zero]
    by_cases h : c = d
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  | succ j ih =>
    rw [pow_succ, Matrix.mul_apply, pow_succ]
    have hN0 : 0 ≤ ∑ a, ∑ b, ‖B a b‖ := by positivity
    have hN : ∑ e, ‖B e d‖ ≤ ∑ a, ∑ b, ‖B a b‖ := by
      refine Finset.sum_le_sum fun e _ => ?_
      exact Finset.single_le_sum (f := fun b => ‖B e b‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ d)
    calc ‖∑ e, (B ^ j) c e * B e d‖ ≤ ∑ e, ‖(B ^ j) c e * B e d‖ := norm_sum_le _ _
      _ ≤ ∑ e, (∑ a, ∑ b, ‖B a b‖) ^ j * ‖B e d‖ := by
          refine Finset.sum_le_sum fun e _ => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (ih c e) (norm_nonneg _)
      _ = (∑ a, ∑ b, ‖B a b‖) ^ j * ∑ e, ‖B e d‖ := by rw [Finset.mul_sum]
      _ ≤ (∑ a, ∑ b, ‖B a b‖) ^ j * ∑ a, ∑ b, ‖B a b‖ :=
          mul_le_mul_of_nonneg_left hN (pow_nonneg hN0 _)

/- English proof (translation)
Use `Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) (Real.summable_pow_div_factorial (‖(s : ℂ)‖ * ∑ a, ∑ b, ‖B a b‖))` and prove the remaining obligations. Rewrite using `[norm_mul, norm_div, norm_pow, Complex.norm_natCast]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `coefC_pow_entry_le B j c d`. Use `_ = (‖(s : ℂ)‖ * ∑ a, ∑ b, ‖B a b‖) ^ j / (j.factorial : ℝ) := by ring`.
-/
theorem coefC_exp_entry_summable (B : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (c d : Fin n) :
    Summable fun j : ℕ => ‖(s : ℂ) ^ j / (j.factorial : ℂ) * (B ^ j) c d‖ := by
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (Real.summable_pow_div_factorial (‖(s : ℂ)‖ * ∑ a, ∑ b, ‖B a b‖))
  rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
  calc ‖(s : ℂ)‖ ^ j / (j.factorial : ℝ) * ‖(B ^ j) c d‖
      ≤ ‖(s : ℂ)‖ ^ j / (j.factorial : ℝ) * (∑ a, ∑ b, ‖B a b‖) ^ j := by
        gcongr
        exact coefC_pow_entry_le B j c d
    _ = (‖(s : ℂ)‖ * ∑ a, ∑ b, ‖B a b‖) ^ j / (j.factorial : ℝ) := by ring

/- English proof (translation)
Establish `hterm : ∀ j : ℕ, ((j.factorial : ℂ))⁻¹ • ((s : ℂ) • B) ^ j = fun c d => (s : ℂ) ^ j / (j.factorial : ℂ) * (B ^ j) c d`. Introduce `j`. Use extensionality with `c d`. Simplify using `only [smul_pow, Matrix.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hS : Summable fun j : ℕ => ((j.factorial : ℂ))⁻¹ • ((s : ℂ) • B) ^ j`. Rewrite using `[show (fun j : ℕ => ((j.factorial : ℂ))⁻¹ • ((s : ℂ) • B) ^ j) = fun j : ℕ => (fun c d => (s : ℂ) ^ j / (j.factorial : ℂ) * (B ^ j) c d) from funext hterm]`. Conclude with `Pi.summable.mpr fun c => Pi.summable.mpr fun d => (coefC_exp_entry_summable B s c d).of_norm`. Establish `hE : NormedSpace.exp ((s : ℂ) • B) = ∑' j : ℕ, ((j.factorial : ℂ))⁻¹ • ((s : ℂ) • B) ^ j`. Rewrite using `[NormedSpace.exp_eq_tsum ℂ]`.

Establish `h2` using `Pi.hasSum.mp (Pi.hasSum.mp hS.hasSum c) d`. Rewrite using `[hE]`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Rewrite using `[hterm j]`.
-/
theorem coefC_exp_entry_hasSum (B : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (c d : Fin n) :
    HasSum (fun j : ℕ => (s : ℂ) ^ j / (j.factorial : ℂ) * (B ^ j) c d)
      ((NormedSpace.exp ((s : ℂ) • B)) c d) := by
  have hterm : ∀ j : ℕ, ((j.factorial : ℂ))⁻¹ • ((s : ℂ) • B) ^ j =
      fun c d => (s : ℂ) ^ j / (j.factorial : ℂ) * (B ^ j) c d := by
    intro j
    ext c d
    simp only [smul_pow, Matrix.smul_apply, smul_eq_mul]
    ring
  have hS : Summable fun j : ℕ => ((j.factorial : ℂ))⁻¹ • ((s : ℂ) • B) ^ j := by
    rw [show (fun j : ℕ => ((j.factorial : ℂ))⁻¹ • ((s : ℂ) • B) ^ j) =
      fun j : ℕ => (fun c d => (s : ℂ) ^ j / (j.factorial : ℂ) * (B ^ j) c d) from funext hterm]
    exact Pi.summable.mpr fun c => Pi.summable.mpr fun d => (coefC_exp_entry_summable B s c d).of_norm
  have hE : NormedSpace.exp ((s : ℂ) • B) = ∑' j : ℕ, ((j.factorial : ℂ))⁻¹ • ((s : ℂ) • B) ^ j := by
    rw [NormedSpace.exp_eq_tsum ℂ]
  have h2 := Pi.hasSum.mp (Pi.hasSum.mp hS.hasSum c) d
  rw [hE]
  convert h2 using 1
  funext j
  rw [hterm j]

/- English proof (translation)
Establish `hs` using `summable_norm_sum_mul_antidiagonal_of_summable_norm hf' hg'`. Establish `h` using `(Summable.of_norm hs).hasSum`. Rewrite `h` using `[← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf' hg', hf.tsum_eq, hg.tsum_eq]`. Conclude with `h`.
-/
theorem coefC_hasSum_mul {f g : ℕ → ℂ} {a b : ℂ} (hf : HasSum f a) (hg : HasSum g b)
    (hf' : Summable fun j => ‖f j‖) (hg' : Summable fun j => ‖g j‖) :
    HasSum (fun m => ∑ kl ∈ antidiagonal m, f kl.1 * g kl.2) (a * b) := by
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm hf' hg'
  have h := (Summable.of_norm hs).hasSum
  rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf' hg', hf.tsum_eq, hg.tsum_eq] at h
  exact h

/- English proof (translation)
Establish `h1 : ((j + k).factorial : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)`. Establish `h2 : (j.factorial : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)`. Establish `h3 : (k.factorial : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)`. Rewrite using `[Nat.cast_choose ℂ (Nat.le_add_right j k), Nat.add_sub_cancel_left, pow_add]`. Apply the tactic sequence `field_simp <;> ring`.
-/
theorem coefC_choose_coef (s : ℂ) (j k : ℕ) :
    s ^ (j + k) / ((j + k).factorial : ℂ) * ((j + k).choose j : ℂ) =
      s ^ j / (j.factorial : ℂ) * (s ^ k / (k.factorial : ℂ)) := by
  have h1 : ((j + k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [Nat.cast_choose ℂ (Nat.le_add_right j k), Nat.add_sub_cancel_left, pow_add]
  field_simp <;> ring

end ReciprocityTheory.ChartRestriction.DS

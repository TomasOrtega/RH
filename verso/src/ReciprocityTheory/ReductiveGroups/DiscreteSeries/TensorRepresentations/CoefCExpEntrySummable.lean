import Mathlib

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

/- English proof (translation)
Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Treat this case separately. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
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
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem coefC_hasSum_mul {f g : ℕ → ℂ} {a b : ℂ} (hf : HasSum f a) (hg : HasSum g b)
    (hf' : Summable fun j => ‖f j‖) (hg' : Summable fun j => ‖g j‖) :
    HasSum (fun m => ∑ kl ∈ antidiagonal m, f kl.1 * g kl.2) (a * b) := by
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm hf' hg'
  have h := (Summable.of_norm hs).hasSum
  rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf' hg', hf.tsum_eq, hg.tsum_eq] at h
  exact h

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
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

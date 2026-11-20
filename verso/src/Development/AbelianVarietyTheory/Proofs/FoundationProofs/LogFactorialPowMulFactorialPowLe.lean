import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `n R₀ R hR hR₀`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Establish `hn1 : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hf1 : (0 : ℝ) < (n.factorial : ℝ)` using `by exact_mod_cast n.factorial_pos`.

Establish `hf2 : (0 : ℝ) < (R₀.factorial : ℝ)` using `by exact_mod_cast R₀.factorial_pos`. Establish `hln : 0 ≤ Real.log (n : ℝ)` using `Real.log_nonneg hn1`. Establish `hlR : 0 ≤ Real.log R` using `Real.log_nonneg hR`. Establish `h0 : (0 : ℝ) ≤ (R₀ : ℝ)` using `Nat.cast_nonneg _`. Establish `h1 : Real.log (n.factorial : ℝ) ≤ n * Real.log n`.

Rewrite using `[← Real.log_pow]`. Apply `Real.log_le_log hf1` to reduce the goal to its premises. Conclude with `n.factorial_le_pow` after adjusting the coercions. Establish `h2 : Real.log (R₀.factorial : ℝ) ≤ R * Real.log R`. Establish `h3 : (R₀.factorial : ℝ) ≤ R ^ R₀`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Establish `hlf : 0 ≤ Real.log (n.factorial : ℝ)` using `Real.log_nonneg (by exact_mod_cast n.factorial_pos)`. Use `push_cast`. Rewrite using `[Real.log_mul (pow_pos hf1 _).ne' (pow_pos hf2 _).ne', Real.log_pow, Real.log_pow, Real.log_mul (by linarith) (by linarith)]`.

Use `push_cast`. Establish `h4 : (R₀ : ℝ) * Real.log (n.factorial : ℝ) ≤ R * (n * Real.log n)` using `mul_le_mul hR₀ h1 hlf (by linarith)`. Establish `h5 : (n : ℝ) * Real.log (R₀.factorial : ℝ) ≤ n * (R * Real.log R)` using `mul_le_mul_of_nonneg_left h2 (by linarith)`. Establish `h6 : 0 ≤ R * (n * Real.log n)` using `by positivity`. Establish `h7 : 0 ≤ (n : ℝ) * (R * Real.log R)` using `by positivity`.

Use polynomial arithmetic with `[h4, h5, h6, h7]`.
-/
theorem log_factorial_pow_mul_factorial_pow_le :
    ∀ (n R₀ : ℕ) (R : ℝ), 1 ≤ R → (R₀ : ℝ) ≤ R →
      Real.log (((n.factorial) ^ (2 * R₀) * (R₀.factorial) ^ n : ℕ) : ℝ)
        ≤ 4 * (n : ℝ) * R * Real.log (n * R) := by
  intro n R₀ R hR hR₀
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hf1 : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hf2 : (0 : ℝ) < (R₀.factorial : ℝ) := by exact_mod_cast R₀.factorial_pos
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hlR : 0 ≤ Real.log R := Real.log_nonneg hR
  have h0 : (0 : ℝ) ≤ (R₀ : ℝ) := Nat.cast_nonneg _
  have h1 : Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
    rw [← Real.log_pow]
    apply Real.log_le_log hf1
    exact_mod_cast n.factorial_le_pow
  have h2 : Real.log (R₀.factorial : ℝ) ≤ R * Real.log R := by
    have h3 : (R₀.factorial : ℝ) ≤ R ^ R₀ := by
      calc (R₀.factorial : ℝ) ≤ (R₀ : ℝ) ^ R₀ := by exact_mod_cast R₀.factorial_le_pow
        _ ≤ R ^ R₀ := pow_le_pow_left₀ h0 hR₀ _
    calc Real.log (R₀.factorial : ℝ) ≤ Real.log (R ^ R₀) := Real.log_le_log hf2 h3
      _ = R₀ * Real.log R := Real.log_pow _ _
      _ ≤ R * Real.log R := mul_le_mul_of_nonneg_right hR₀ hlR
  have hlf : 0 ≤ Real.log (n.factorial : ℝ) :=
    Real.log_nonneg (by exact_mod_cast n.factorial_pos)
  push_cast
  rw [Real.log_mul (pow_pos hf1 _).ne' (pow_pos hf2 _).ne', Real.log_pow, Real.log_pow,
    Real.log_mul (by linarith) (by linarith)]
  push_cast
  have h4 : (R₀ : ℝ) * Real.log (n.factorial : ℝ) ≤ R * (n * Real.log n) :=
    mul_le_mul hR₀ h1 hlf (by linarith)
  have h5 : (n : ℝ) * Real.log (R₀.factorial : ℝ) ≤ n * (R * Real.log R) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  have h6 : 0 ≤ R * (n * Real.log n) := by positivity
  have h7 : 0 ≤ (n : ℝ) * (R * Real.log R) := by positivity
  nlinarith [h4, h5, h6, h7]

end GlobalTheory

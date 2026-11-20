import Mathlib

namespace GlobalTheory

/- English proof (translation)
Take `⟨C, hC⟩` from `exists_nat_ge ((d.factorial : ℚ) * ∑ i ∈ Finset.range d, |p.coeff i|)`. Use `⟨C, fun m => ?_⟩` and prove the remaining obligations. Establish `hm : (0 : ℚ) ≤ m` using `Nat.cast_nonneg m`. Establish `hf : (0 : ℚ) ≤ d.factorial` using `Nat.cast_nonneg _`. Rewrite using `[Polynomial.eval_eq_sum_range' (n := d + 1) (Nat.lt_succ_of_le hp), Finset.sum_range_succ]`.

Establish `e : (d.factorial : ℚ) * (∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i + p.coeff d * (m : ℚ) ^ d) - (d.factorial : ℚ) * p.coeff d * (m : ℚ) ^ d = (d.factorial : ℚ) * ∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i` using `by ring`. Rewrite using `[e, abs_mul, abs_of_nonneg hf]`. Establish `hX : (0 : ℚ) ≤ (d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)` using `by positivity`. Establish `h1 : |∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i| ≤ (∑ i ∈ Finset.range d, |p.coeff i|) * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1))`. Rewrite using `[Finset.sum_mul]`.

Use `(Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)` and prove the remaining obligations. Establish `hi' : i < d` using `Finset.mem_range.mp hi`. Rewrite using `[abs_mul, abs_of_nonneg (pow_nonneg hm i)]`. Use `mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)` and prove the remaining obligations. Establish `a1 : (m : ℚ) ^ i ≤ ((m : ℚ) + 1) ^ i` using `pow_le_pow_left₀ hm (by linarith) i`.

Establish `a2 : ((m : ℚ) + 1) ^ i ≤ ((m : ℚ) + 1) ^ (d - 1)` using `pow_le_pow_right₀ (by linarith) (by omega)`. Establish `a3 : (1 : ℚ) ≤ d` using `by exact_mod_cast (show 1 ≤ d by omega)`. Establish `a4 : (0 : ℚ) ≤ ((m : ℚ) + 1) ^ (d - 1)` using `by positivity`. Conclude with `a1.trans (a2.trans (le_mul_of_one_le_left a4 a3))`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem abs_factorial_mul_eval_sub_top_le (d : ℕ) (p : Polynomial ℚ) (hp : p.natDegree ≤ d) :
    ∃ C : ℕ, ∀ m : ℕ, |(d.factorial : ℚ) * p.eval (m : ℚ) - (d.factorial : ℚ) * p.coeff d * (m : ℚ) ^ d|
      ≤ C * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)) := by
  obtain ⟨C, hC⟩ := exists_nat_ge ((d.factorial : ℚ) * ∑ i ∈ Finset.range d, |p.coeff i|)
  refine ⟨C, fun m => ?_⟩
  have hm : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have hf : (0 : ℚ) ≤ d.factorial := Nat.cast_nonneg _
  rw [Polynomial.eval_eq_sum_range' (n := d + 1) (Nat.lt_succ_of_le hp), Finset.sum_range_succ]
  have e : (d.factorial : ℚ) * (∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i + p.coeff d * (m : ℚ) ^ d)
      - (d.factorial : ℚ) * p.coeff d * (m : ℚ) ^ d
      = (d.factorial : ℚ) * ∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i := by ring
  rw [e, abs_mul, abs_of_nonneg hf]
  have hX : (0 : ℚ) ≤ (d : ℚ) * ((m : ℚ) + 1) ^ (d - 1) := by positivity
  have h1 : |∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i|
      ≤ (∑ i ∈ Finset.range d, |p.coeff i|) * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)) := by
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hi' : i < d := Finset.mem_range.mp hi
    rw [abs_mul, abs_of_nonneg (pow_nonneg hm i)]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have a1 : (m : ℚ) ^ i ≤ ((m : ℚ) + 1) ^ i := pow_le_pow_left₀ hm (by linarith) i
    have a2 : ((m : ℚ) + 1) ^ i ≤ ((m : ℚ) + 1) ^ (d - 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have a3 : (1 : ℚ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    have a4 : (0 : ℚ) ≤ ((m : ℚ) + 1) ^ (d - 1) := by positivity
    exact a1.trans (a2.trans (le_mul_of_one_le_left a4 a3))
  calc _ ≤ (d.factorial : ℚ) * ((∑ i ∈ Finset.range d, |p.coeff i|) * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1))) :=
        mul_le_mul_of_nonneg_left h1 hf
    _ = ((d.factorial : ℚ) * ∑ i ∈ Finset.range d, |p.coeff i|) * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC hX

end GlobalTheory

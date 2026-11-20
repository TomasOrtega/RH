import Mathlib
open MeasureTheory
open scoped ComplexOrder

namespace GlobalTheory

/- English proof (translation)
Establish `hRHS : (√(Real.exp 1 * n * i) ^ i * √a ^ i) ^ 2 = (Real.exp 1 * n * i) ^ i * a ^ i`. Rewrite using `[mul_pow, ← pow_mul, ← pow_mul, mul_comm i 2, pow_mul, pow_mul, Real.sq_sqrt (by positivity), Real.sq_sqrt ha]`. Rewrite using `[hRHS]`. Break down `Nat.eq_zero_or_pos i with rfl | hi` into its components or cases. Simplify using `using hb 0`.

Break down `ha.eq_or_lt with rfl | ha'` into its components or cases. Establish `hbd : ∀ t, ‖f t‖ ≤ |S|`. Introduce `t`. Establish `h` using `hb t`. Simplify using `only [mul_zero, zero_mul, Real.exp_zero, mul_one] at h`.

Use `sq_le_sq.mp h` as an intermediate fact. Rewrite `this` using `[abs_norm]`. Then use the resulting hypothesis. Establish `hconst : ∀ z, f z = f 0` using `fun z => hf.apply_eq_apply_of_bounded (isBounded_iff_forall_norm_le.2 ⟨|S|, by rintro _ ⟨t, rfl⟩; exact hbd t⟩) z 0`. Establish `hfe : f = fun _ => f 0` using `funext hconst`. Rewrite using `[hfe]`.

Simplify using `[iteratedDeriv_const, hi.ne']`. Establish `hnpos : (0:ℝ) < n` using `by exact_mod_cast hn`. Establish `hipos : (0:ℝ) < i` using `by exact_mod_cast hi`. Use `set R := √(i / (n * a)) with hRdef`. Establish `hR : 0 < R` using `Real.sqrt_pos.2 (by positivity)`.

Establish `hR2 : R ^ 2 = i / (n * a)` using `Real.sq_sqrt (by positivity)`. Establish `h2 : (|S| * Real.exp (i / 2)) ^ 2 = S ^ 2 * Real.exp i`. Rewrite using `[mul_pow, sq_abs, sq (Real.exp _), ← Real.exp_add, add_halves]`. Establish `hC : ∀ z ∈ Metric.sphere (0:ℂ) R, ‖f z‖ ≤ |S| * Real.exp (i / 2)`. Introduce `z hz`.

Establish `hz' : ‖z‖ = R` using `by simpa using hz`. Establish `h1` using `hb z`. Rewrite `h1` using `[hz', hR2]`. Establish `hc : (n:ℝ) * a * (i / (n * a)) = i` using `by field_simp`. Rewrite `h1` using `[hc, ← h2]`.

Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1`. Establish `hcau` using `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le i hR hf.diffContOnCl hC`. Establish `hsq` using `pow_le_pow_left₀ (norm_nonneg _) hcau 2`. Establish `hfac : ((i.factorial : ℕ) : ℝ) ≤ (i:ℝ) ^ i` using `by exact_mod_cast Nat.factorial_le_pow i`. Establish `hkey : (Real.exp 1 * n * i) ^ i * a ^ i * (i / (n * a)) ^ i = Real.exp i * ((i:ℝ) ^ i) ^ 2`.

Rewrite using `[← mul_pow, ← mul_pow]`. Establish `: Real.exp 1 * n * i * a * (i / (n * a)) = Real.exp 1 * (i:ℝ) ^ 2`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this, mul_pow, ← pow_mul, mul_comm 2 i, pow_mul, ← Real.exp_nat_mul, mul_one]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← hR2, ← h2]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (Real.exp 1 * n * i) ^ i * a ^ i * S ^ 2 := by`. Rewrite using `[div_le_iff₀ (by positivity)]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hkey]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = (Real.exp 1 * n * i) ^ i * a ^ i * S ^ 2 * (i / (n * a)) ^ i := by ring`.
-/
theorem norm_iteratedDeriv_sq_le_of_gaussian_growth (f : ℂ → ℂ) (a S : ℝ) (n i : ℕ)
    (hf : Differentiable ℂ f) (ha : 0 ≤ a) (hn : 1 ≤ n)
    (hb : ∀ t : ℂ, ‖f t‖ ^ 2 ≤ S ^ 2 * Real.exp (n * a * ‖t‖ ^ 2)) :
    ‖iteratedDeriv i f 0‖ ^ 2 ≤ (√(Real.exp 1 * n * i) ^ i * √a ^ i) ^ 2 * S ^ 2 := by
  have hRHS : (√(Real.exp 1 * n * i) ^ i * √a ^ i) ^ 2 = (Real.exp 1 * n * i) ^ i * a ^ i := by
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm i 2, pow_mul, pow_mul,
      Real.sq_sqrt (by positivity), Real.sq_sqrt ha]
  rw [hRHS]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simpa using hb 0
  rcases ha.eq_or_lt with rfl | ha'
  · have hbd : ∀ t, ‖f t‖ ≤ |S| := by
      intro t
      have h := hb t
      simp only [mul_zero, zero_mul, Real.exp_zero, mul_one] at h
      have := sq_le_sq.mp h
      rwa [abs_norm] at this
    have hconst : ∀ z, f z = f 0 := fun z =>
      hf.apply_eq_apply_of_bounded
        (isBounded_iff_forall_norm_le.2 ⟨|S|, by rintro _ ⟨t, rfl⟩; exact hbd t⟩) z 0
    have hfe : f = fun _ => f 0 := funext hconst
    rw [hfe]
    simp [iteratedDeriv_const, hi.ne']
  · have hnpos : (0:ℝ) < n := by exact_mod_cast hn
    have hipos : (0:ℝ) < i := by exact_mod_cast hi
    set R := √(i / (n * a)) with hRdef
    have hR : 0 < R := Real.sqrt_pos.2 (by positivity)
    have hR2 : R ^ 2 = i / (n * a) := Real.sq_sqrt (by positivity)
    have h2 : (|S| * Real.exp (i / 2)) ^ 2 = S ^ 2 * Real.exp i := by
      rw [mul_pow, sq_abs, sq (Real.exp _), ← Real.exp_add, add_halves]
    have hC : ∀ z ∈ Metric.sphere (0:ℂ) R, ‖f z‖ ≤ |S| * Real.exp (i / 2) := by
      intro z hz
      have hz' : ‖z‖ = R := by simpa using hz
      have h1 := hb z
      rw [hz', hR2] at h1
      have hc : (n:ℝ) * a * (i / (n * a)) = i := by field_simp
      rw [hc, ← h2] at h1
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1
    have hcau := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le i hR
      hf.diffContOnCl hC
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hcau 2
    have hfac : ((i.factorial : ℕ) : ℝ) ≤ (i:ℝ) ^ i := by exact_mod_cast Nat.factorial_le_pow i
    have hkey : (Real.exp 1 * n * i) ^ i * a ^ i * (i / (n * a)) ^ i
        = Real.exp i * ((i:ℝ) ^ i) ^ 2 := by
      rw [← mul_pow, ← mul_pow]
      have : Real.exp 1 * n * i * a * (i / (n * a)) = Real.exp 1 * (i:ℝ) ^ 2 := by
        field_simp
      rw [this, mul_pow, ← pow_mul, mul_comm 2 i, pow_mul, ← Real.exp_nat_mul, mul_one]
    calc ‖iteratedDeriv i f 0‖ ^ 2
        ≤ ((i.factorial : ℝ) * (|S| * Real.exp (i / 2)) / R ^ i) ^ 2 := hsq
      _ = (i.factorial : ℝ) ^ 2 * (S ^ 2 * Real.exp i) / (i / (n * a)) ^ i := by
        rw [← hR2, ← h2]; ring
      _ ≤ (Real.exp 1 * n * i) ^ i * a ^ i * S ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        calc (i.factorial : ℝ) ^ 2 * (S ^ 2 * Real.exp i)
            ≤ ((i:ℝ) ^ i) ^ 2 * (S ^ 2 * Real.exp i) :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hfac 2) (by positivity)
          _ = (Real.exp 1 * n * i) ^ i * a ^ i * (i / (n * a)) ^ i * S ^ 2 := by
              rw [hkey]; ring
          _ = (Real.exp 1 * n * i) ^ i * a ^ i * S ^ 2 * (i / (n * a)) ^ i := by ring

end GlobalTheory

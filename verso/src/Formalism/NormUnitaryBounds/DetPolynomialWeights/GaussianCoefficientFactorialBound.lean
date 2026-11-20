import Formalism.NormUnitaryBounds.Statement
import Formalism.NormUnitaryBounds.DetPolynomialWeights.IntegralExpInt

open MeasureTheory Complex

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas

open ExponentialIntegralMeasures

/- English proof (translation)
Use `set r : Fin G → ℝ := fun i => Real.sqrt (e i) with hr`. Establish `hB : ∀ θ : Fin G → ℝ, ‖Θ (fun i => (r i : ℂ) * Complex.exp ((θ i : ℂ) * I))‖ ≤ S * Real.exp ((∑ i, (e i : ℝ)) / 2)`. Introduce `θ`. Establish `h` using `hS (fun i => (r i : ℂ) * Complex.exp ((θ i : ℂ) * I))`. Establish `hz : ∀ i, ‖(r i : ℂ) * Complex.exp ((θ i : ℂ) * I)‖ ^ 2 = (e i : ℝ)`.

Introduce `i`. Rewrite using `[norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs, hr, Real.sq_sqrt (Nat.cast_nonneg _)]`. Simplify using `only [hz] at h`. Conclude with `h`. Establish `h1` using `cauchy_torus G Θ c hΘ r _ hB e`.

Establish `hr' : ∀ i, |r i| = Real.sqrt (e i)` using `fun i => abs_of_nonneg (Real.sqrt_nonneg _)`. Simplify using `only [hr'] at h1`. Establish `h0 : 0 ≤ ‖c e‖ * ∏ i, Real.sqrt (e i) ^ e i` using `by positivity`. Establish `h2` using `pow_le_pow_left₀ h0 h1 2`. Establish `hl : (‖c e‖ * ∏ i, Real.sqrt (e i) ^ e i) ^ 2 = ‖c e‖ ^ 2 * ∏ i, ((e i : ℝ)) ^ e i`.

Rewrite using `[mul_pow, ← Finset.prod_pow]`. Use `congr 1`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]`.

Establish `hrr : (S * Real.exp ((∑ i, (e i : ℝ)) / 2)) ^ 2 = S ^ 2 * Real.exp (∑ i, (e i : ℝ))`. Rewrite using `[mul_pow, sq (Real.exp _), ← Real.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[hl, hrr]`.

Conclude with `h2`.
-/
lemma norm_sq_coeff_le_gaussian_growth (G : ℕ) (Θ : (Fin G → ℂ) → ℂ) (c : (Fin G → ℕ) → ℂ) (S : ℝ)
    (hΘ : ∀ z : Fin G → ℂ, HasSum (fun e : Fin G → ℕ => c e * ∏ i, z i ^ e i) (Θ z))
    (hS : ∀ z : Fin G → ℂ, ‖Θ z‖ ≤ S * Real.exp ((∑ i, ‖z i‖ ^ 2) / 2))
    (e : Fin G → ℕ) :
    ‖c e‖ ^ 2 * ∏ i, ((e i : ℝ)) ^ e i ≤ S ^ 2 * Real.exp (∑ i, (e i : ℝ)) := by
  set r : Fin G → ℝ := fun i => Real.sqrt (e i) with hr
  have hB : ∀ θ : Fin G → ℝ, ‖Θ (fun i => (r i : ℂ) * Complex.exp ((θ i : ℂ) * I))‖ ≤
      S * Real.exp ((∑ i, (e i : ℝ)) / 2) := by
    intro θ
    have h := hS (fun i => (r i : ℂ) * Complex.exp ((θ i : ℂ) * I))
    have hz : ∀ i, ‖(r i : ℂ) * Complex.exp ((θ i : ℂ) * I)‖ ^ 2 = (e i : ℝ) := by
      intro i
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        sq_abs, hr, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp only [hz] at h
    exact h
  have h1 := cauchy_torus G Θ c hΘ r _ hB e
  have hr' : ∀ i, |r i| = Real.sqrt (e i) := fun i => abs_of_nonneg (Real.sqrt_nonneg _)
  simp only [hr'] at h1
  have h0 : 0 ≤ ‖c e‖ * ∏ i, Real.sqrt (e i) ^ e i := by positivity
  have h2 := pow_le_pow_left₀ h0 h1 2
  have hl : (‖c e‖ * ∏ i, Real.sqrt (e i) ^ e i) ^ 2 = ‖c e‖ ^ 2 * ∏ i, ((e i : ℝ)) ^ e i := by
    rw [mul_pow, ← Finset.prod_pow]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hrr : (S * Real.exp ((∑ i, (e i : ℝ)) / 2)) ^ 2 = S ^ 2 * Real.exp (∑ i, (e i : ℝ)) := by
    rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
    congr 2; ring
  rw [hl, hrr] at h2
  exact h2

/- English proof (translation)
Introduce `G Θ c S hΘ hS e`. Establish `h` using `norm_sq_coeff_le_gaussian_growth G Θ c S hΘ hS e`. Establish `hpos : 0 < ∏ i, ((e i : ℝ)) ^ e i`. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `i _`.

Break down `Nat.eq_zero_or_pos (e i) with h0 | h0` into its components or cases. Rewrite using `[h0]`. Simplify using the standard rewrite rules. Check the signs of the components of the expression. Establish `hprod : ∏ i, (Real.exp 1 / (e i : ℝ)) ^ e i = Real.exp (∑ i, (e i : ℝ)) / ∏ i, ((e i : ℝ)) ^ e i`.

Repeatedly rewrite using `[div_pow]`. Rewrite using `[Finset.prod_div_distrib, Real.exp_sum]`. Use `congr 1`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `i _`.

Rewrite using `[← Real.exp_nat_mul, mul_one]`. Rewrite using `[hprod, ← mul_div_assoc, le_div_iff₀ hpos]`. Conclude with `h`.
-/
theorem gaussian_coefficient_bound_holds : N1 := by
  intro G Θ c S hΘ hS e
  have h := norm_sq_coeff_le_gaussian_growth G Θ c S hΘ hS e
  have hpos : 0 < ∏ i, ((e i : ℝ)) ^ e i := by
    apply Finset.prod_pos
    intro i _
    rcases Nat.eq_zero_or_pos (e i) with h0 | h0
    · rw [h0]; simp
    · positivity
  have hprod : ∏ i, (Real.exp 1 / (e i : ℝ)) ^ e i =
      Real.exp (∑ i, (e i : ℝ)) / ∏ i, ((e i : ℝ)) ^ e i := by
    simp_rw [div_pow]
    rw [Finset.prod_div_distrib, Real.exp_sum]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [← Real.exp_nat_mul, mul_one]
  rw [hprod, ← mul_div_assoc, le_div_iff₀ hpos]
  exact h

end Formalism.NormUnitaryCountingLemmas

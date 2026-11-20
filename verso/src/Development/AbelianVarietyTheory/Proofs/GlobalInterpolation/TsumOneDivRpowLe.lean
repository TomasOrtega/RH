import Mathlib
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.LLower

/- English proof (translation)
Establish `hσ0 : 0 < σ` using `by linarith`. Establish `anti : AntitoneOn (fun t : ℝ => t ^ (-σ)) (Set.Ici ((1 : ℕ) : ℝ))`. Introduce `x hx y hy hxy`. Simplify using `only [Set.mem_Ici, Nat.cast_one] at hx hy`. Conclude with `Real.rpow_le_rpow_of_nonpos (by linarith) hxy (by linarith)`.

Establish `integ : IntegrableOn (fun t : ℝ => t ^ (-σ)) (Set.Ioi ((1 : ℕ) : ℝ))`. Simplify using `using integrableOn_Ioi_rpow_of_lt (by linarith : -σ < -1) zero_lt_one`. Establish `nonneg : ∀ t ∈ Set.Ioi ((1 : ℕ) : ℝ), 0 ≤ (fun t : ℝ => t ^ (-σ)) t`. Introduce `t ht`. Simplify using `only [Set.mem_Ioi, Nat.cast_one] at ht`.

Conclude with `Real.rpow_nonneg (by linarith) _`. Establish `key` using `anti.tsum_comp_add_le_integral 1 integ nonneg`. Establish `hI : ∫ t in Set.Ioi ((1 : ℕ) : ℝ), t ^ (-σ) = 1 / (σ - 1)`. Rewrite using `[Nat.cast_one, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]`. Establish `: σ - 1 ≠ 0` using `by linarith`.

Establish `: -σ + 1 ≠ 0` using `by linarith`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[hI]`. Establish `hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ σ)`.

Use `(summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hσ)` as an intermediate fact. Simplify `this` using `[Nat.cast_add, Nat.cast_one]`. Rewrite using `[hs.tsum_eq_zero_add]`. Establish `heq : ∀ n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) + 1) ^ σ = ((n + 1 + 1 : ℕ) : ℝ) ^ (-σ)`. Introduce `n`.

Rewrite using `[Real.rpow_neg (by positivity), one_div]`. Use `push_cast`. Put the polynomial expressions in normal form. Simplify using `only [heq] at *`. Establish `h0 : (1 : ℝ) / ((0 : ℕ) + 1 : ℝ) ^ σ = 1` using `by simp`.

Rewrite using `[h0]`. Establish `: σ / (σ - 1) = 1 + 1 / (σ - 1)`. Establish `: σ - 1 ≠ 0` using `by linarith`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem tsum_one_div_rpow_le {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ σ ≤ σ / (σ - 1) := by
  have hσ0 : 0 < σ := by linarith
  have anti : AntitoneOn (fun t : ℝ => t ^ (-σ)) (Set.Ici ((1 : ℕ) : ℝ)) := by
    intro x hx y hy hxy
    simp only [Set.mem_Ici, Nat.cast_one] at hx hy
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hxy (by linarith)
  have integ : IntegrableOn (fun t : ℝ => t ^ (-σ)) (Set.Ioi ((1 : ℕ) : ℝ)) := by
    simpa using integrableOn_Ioi_rpow_of_lt (by linarith : -σ < -1) zero_lt_one
  have nonneg : ∀ t ∈ Set.Ioi ((1 : ℕ) : ℝ), 0 ≤ (fun t : ℝ => t ^ (-σ)) t := by
    intro t ht
    simp only [Set.mem_Ioi, Nat.cast_one] at ht
    exact Real.rpow_nonneg (by linarith) _
  have key := anti.tsum_comp_add_le_integral 1 integ nonneg
  have hI : ∫ t in Set.Ioi ((1 : ℕ) : ℝ), t ^ (-σ) = 1 / (σ - 1) := by
    rw [Nat.cast_one, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
    have : σ - 1 ≠ 0 := by linarith
    have : -σ + 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [hI] at key
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ σ) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hσ)
    simpa [Nat.cast_add, Nat.cast_one] using this
  rw [hs.tsum_eq_zero_add]
  have heq : ∀ n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) + 1) ^ σ = ((n + 1 + 1 : ℕ) : ℝ) ^ (-σ) := by
    intro n
    rw [Real.rpow_neg (by positivity), one_div]
    push_cast
    ring_nf
  simp only [heq] at *
  have h0 : (1 : ℝ) / ((0 : ℕ) + 1 : ℝ) ^ σ = 1 := by simp
  rw [h0]
  have : σ / (σ - 1) = 1 + 1 / (σ - 1) := by
    have : σ - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [this]
  linarith

/- English proof (translation)
Establish `hσ : 1 < s.re` using `hs`. Establish `hg : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ s.re) (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s.re)`. Establish `hsum` using `Real.summable_one_div_nat_rpow.mpr hσ`. Use `hsum.hasSum` as an intermediate fact. Rewrite `this` using `[hsum.tsum_eq_zero_add]`.

Simplify `this` using `[Real.zero_rpow (by linarith : s.re ≠ 0)]`. Use `(tsum_of_norm_bounded hg fun n => ?_).trans (tsum_one_div_rpow_le hσ)` and prove the remaining obligations. Rewrite using `[LSeries.norm_term_eq]`. Use `split_ifs with hn`. Substitute `hn` using the available equality.

Simplify using `[Real.zero_rpow (by linarith : s.re ≠ 0)]`. Establish `hpos : 0 < (n : ℝ) ^ s.re` using `Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _`. Conclude with `div_le_div_of_nonneg_right (hf n) hpos.le`.
-/
theorem norm_LSeries_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries f s‖ ≤ s.re / (s.re - 1) := by
  have hσ : 1 < s.re := hs
  have hg : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ s.re) (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s.re) := by
    have hsum := Real.summable_one_div_nat_rpow.mpr hσ
    have := hsum.hasSum
    rw [hsum.tsum_eq_zero_add] at this
    simpa [Real.zero_rpow (by linarith : s.re ≠ 0)] using this
  refine (tsum_of_norm_bounded hg fun n => ?_).trans (tsum_one_div_rpow_le hσ)
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · subst hn
    simp [Real.zero_rpow (by linarith : s.re ≠ 0)]
  · have hpos : 0 < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _
    exact div_le_div_of_nonneg_right (hf n) hpos.le

/- English proof (translation)
Establish `hre : 1 < s.re` using `hs`. Establish `hσ : 0 < s.re` using `by linarith`. Establish `hprod` using `DirichletCharacter.LSeries.mul_mu_eq_one χ hs`. Rewrite using `[DirichletCharacter.LFunction_eq_LSeries χ hs]`. Establish `hb : ‖LSeries (fun n => χ n * (moebius n : ℂ)) s‖ ≤ s.re / (s.re - 1)`.

Use `norm_LSeries_le (fun n => ?_) hre` and prove the remaining obligations. Rewrite using `[norm_mul]`. Establish `h1 : ‖χ n‖ ≤ 1` using `DirichletCharacter.norm_le_one χ n`. Establish `h2 : ‖((moebius n : ℤ) : ℂ)‖ ≤ 1`. Rewrite using `[Complex.norm_intCast]`.

Conclude with `abs_moebius_le_one` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Establish `hn : ‖LSeries (fun n => (χ n : ℂ)) s‖ * ‖LSeries (fun n => χ n * (moebius n : ℂ)) s‖ = 1`. Establish `hprod' : LSeries (fun n => (χ n : ℂ)) s * LSeries (fun n => χ n * (moebius n : ℂ)) s = 1` using `hprod`. Rewrite using `[← norm_mul, hprod', norm_one]`.

Establish `hd : 0 < s.re - 1` using `by linarith`. Rewrite using `[div_le_iff₀ hσ]`. Establish `hA : 0 ≤ ‖LSeries (fun n => (χ n : ℂ)) s‖` using `norm_nonneg _`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts.
-/
theorem norm_LFunction_ge (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : 1 < s.re) : (s.re - 1) / s.re ≤ ‖LFunction χ s‖ := by
  have hre : 1 < s.re := hs
  have hσ : 0 < s.re := by linarith
  have hprod := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hb : ‖LSeries (fun n => χ n * (moebius n : ℂ)) s‖ ≤ s.re / (s.re - 1) := by
    refine norm_LSeries_le (fun n => ?_) hre
    rw [norm_mul]
    have h1 : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
    have h2 : ‖((moebius n : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast abs_moebius_le_one
    calc ‖χ n‖ * ‖((moebius n : ℤ) : ℂ)‖ ≤ 1 * 1 :=
          mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hn : ‖LSeries (fun n => (χ n : ℂ)) s‖ * ‖LSeries (fun n => χ n * (moebius n : ℂ)) s‖ = 1 := by
    have hprod' : LSeries (fun n => (χ n : ℂ)) s * LSeries (fun n => χ n * (moebius n : ℂ)) s = 1 :=
      hprod
    rw [← norm_mul, hprod', norm_one]
  have hd : 0 < s.re - 1 := by linarith
  rw [div_le_iff₀ hσ]
  have hA : 0 ≤ ‖LSeries (fun n => (χ n : ℂ)) s‖ := norm_nonneg _
  calc s.re - 1 = (s.re - 1) * (‖LSeries (fun n => (χ n : ℂ)) s‖ *
        ‖LSeries (fun n => χ n * (moebius n : ℂ)) s‖) := by rw [hn, mul_one]
    _ ≤ (s.re - 1) * (‖LSeries (fun n => (χ n : ℂ)) s‖ * (s.re / (s.re - 1))) := by
        gcongr
    _ = ‖LSeries (fun n => (χ n : ℂ)) s‖ * s.re := by
        field_simp

end GlobalTheory.LLower

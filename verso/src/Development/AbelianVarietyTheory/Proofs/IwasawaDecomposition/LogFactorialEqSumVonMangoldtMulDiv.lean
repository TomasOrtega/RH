import Mathlib
open Finset ArithmeticFunction

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[← ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (R := ℝ) Λ N, vonMangoldt_mul_zeta]`. Proceed by induction on `N with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[Finset.sum_Ioc_succ_top (Nat.zero_le k), ← ih, Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity), add_comm]`.

Both sides reduce to the same expression.
-/
theorem log_factorial_eq_sum_vonMangoldt_mul_div (N : ℕ) :
    Real.log (N.factorial : ℝ) = ∑ n ∈ Ioc 0 N, Λ n * ((N / n : ℕ) : ℝ) := by
  rw [← ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (R := ℝ) Λ N, vonMangoldt_mul_zeta]
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le k), ← ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity), add_comm]
    rfl

/- English proof (translation)
Establish `hN' : (0 : ℝ) < N` using `by exact_mod_cast hN`. Establish `hF` using `log_factorial_eq_sum_vonMangoldt_mul_div N`. Establish `hfp : (0 : ℝ) < N.factorial` using `by exact_mod_cast N.factorial_pos`. Establish `hup : Real.log (N.factorial : ℝ) ≤ N * Real.log N`. Rewrite using `[← Real.log_pow]`.

Conclude with `Real.log_le_log hfp (by exact_mod_cast N.factorial_le_pow)`. Establish `hlo : N * Real.log N - N ≤ Real.log (N.factorial : ℝ)`. Establish `h1` using `Real.pow_div_factorial_le_exp (N : ℝ) hN'.le N`. Establish `h2` using `Real.log_le_log (by positivity) h1`. Rewrite `h2` using `[Real.log_exp, Real.log_div (by positivity) hfp.ne', Real.log_pow]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : Real.log (N.factorial : ℝ) ≤ N * ∑ n ∈ Ioc 0 N, Λ n / (n : ℝ)`. Rewrite using `[hF, Finset.mul_sum]`. Use `Finset.sum_le_sum fun n _ => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Establish `h2 : N * ∑ n ∈ Ioc 0 N, Λ n / (n : ℝ) ≤ Real.log (N.factorial : ℝ) + ∑ n ∈ Ioc 0 N, Λ n`. Rewrite using `[hF, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum fun n hn => ?_` and prove the remaining obligations. Establish `hn0 : 0 < n` using `(Finset.mem_Ioc.mp hn).1`. Establish `hn' : (0 : ℝ) < n` using `by exact_mod_cast hn0`.

Establish `hlt : (N : ℝ) / n ≤ ((N / n : ℕ) : ℝ) + 1`. Rewrite using `[div_le_iff₀ hn']`. Establish `h` using `Nat.lt_div_mul_add (a := N) hn0`. Establish `h' : (N : ℝ) < ((N / n : ℕ) : ℝ) * n + n` using `by exact_mod_cast h`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation. Establish `h3 : ∑ n ∈ Ioc 0 N, Λ n ≤ (Real.log 4 + 4) * N`. Establish `h` using `Chebyshev.psi_le_const_mul_self hN'.le`. Rewrite `h` using `[Chebyshev.psi, Nat.floor_natCast]`. Then use the resulting hypothesis. Prove the components needed by the constructor for the conclusion.

Use `le_of_mul_le_mul_left ?_ hN'` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities. Use `le_of_mul_le_mul_left ?_ hN'` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sum_vonMangoldt_div_nat_bounds (N : ℕ) (hN : 1 ≤ N) :
    Real.log N - 1 ≤ ∑ n ∈ Ioc 0 N, Λ n / (n : ℝ) ∧
      ∑ n ∈ Ioc 0 N, Λ n / (n : ℝ) ≤ Real.log N + (Real.log 4 + 4) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hF := log_factorial_eq_sum_vonMangoldt_mul_div N
  have hfp : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  have hup : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
    rw [← Real.log_pow]
    exact Real.log_le_log hfp (by exact_mod_cast N.factorial_le_pow)
  have hlo : N * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
    have h1 := Real.pow_div_factorial_le_exp (N : ℝ) hN'.le N
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_exp, Real.log_div (by positivity) hfp.ne', Real.log_pow] at h2
    linarith
  have h1 : Real.log (N.factorial : ℝ) ≤ N * ∑ n ∈ Ioc 0 N, Λ n / (n : ℝ) := by
    rw [hF, Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    calc Λ n * ((N / n : ℕ) : ℝ) ≤ Λ n * ((N : ℝ) / n) :=
          mul_le_mul_of_nonneg_left Nat.cast_div_le vonMangoldt_nonneg
      _ = N * (Λ n / n) := by ring
  have h2 : N * ∑ n ∈ Ioc 0 N, Λ n / (n : ℝ) ≤
      Real.log (N.factorial : ℝ) + ∑ n ∈ Ioc 0 N, Λ n := by
    rw [hF, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hlt : (N : ℝ) / n ≤ ((N / n : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hn']
      have h := Nat.lt_div_mul_add (a := N) hn0
      have h' : (N : ℝ) < ((N / n : ℕ) : ℝ) * n + n := by exact_mod_cast h
      linarith
    calc (N : ℝ) * (Λ n / n) = Λ n * ((N : ℝ) / n) := by ring
      _ ≤ Λ n * (((N / n : ℕ) : ℝ) + 1) := mul_le_mul_of_nonneg_left hlt vonMangoldt_nonneg
      _ = _ := by ring
  have h3 : ∑ n ∈ Ioc 0 N, Λ n ≤ (Real.log 4 + 4) * N := by
    have h := Chebyshev.psi_le_const_mul_self hN'.le
    rwa [Chebyshev.psi, Nat.floor_natCast] at h
  constructor
  · refine le_of_mul_le_mul_left ?_ hN'
    nlinarith
  · refine le_of_mul_le_mul_left ?_ hN'
    nlinarith

/- English proof (translation)
The claim follows from `|∑ n ∈ Icc 1 ⌊y⌋₊, Λ n / (n : ℝ) - Real.log y| ≤ CM := by have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num) refine ⟨Real.log 4 + 4, by positivity, fun y hy => ?_⟩ have hN : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy) have hN' : (1 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hN h …`.
-/
theorem mertens_first_vonMangoldt :
    ∃ CM : ℝ, 0 ≤ CM ∧ ∀ y : ℝ, 1 ≤ y →
      |∑ n ∈ Icc 1 ⌊y⌋₊, Λ n / (n : ℝ) - Real.log y| ≤ CM := by
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨Real.log 4 + 4, by positivity, fun y hy => ?_⟩
  have hN : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy)
  have hN' : (1 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hN
  have hI : Icc 1 ⌊y⌋₊ = Ioc 0 ⌊y⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  obtain ⟨h1, h2⟩ := sum_vonMangoldt_div_nat_bounds _ hN
  have h5 : Real.log ⌊y⌋₊ ≤ Real.log y :=
    Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  have h6 : Real.log y ≤ Real.log 4 + Real.log ⌊y⌋₊ := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    refine Real.log_le_log (by linarith) ?_
    have := Nat.lt_floor_add_one y
    linarith
  rw [hI, abs_le]
  constructor <;> linarith

end GlobalTheory

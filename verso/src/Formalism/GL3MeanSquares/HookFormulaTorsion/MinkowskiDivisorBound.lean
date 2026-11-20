import Mathlib
import Formalism.GL3MeanSquares.ConcavityEquidistribution

namespace Formalism.HermitianLattices.TraceIntegrality

open Finset

/- English proof (translation)
Establish `hpos : 0 < p ^ (1 + i)` using `Nat.pow_pos (by omega)`. Rewrite using `[Nat.le_div_iff_mul_le hpos]`. Establish `h1 : n / (p ^ i * (p - 1)) * (p ^ i * (p - 1)) ≤ n` using `Nat.div_mul_le_self _ _`. Establish `h2 : p ≤ 2 * (p - 1)` using `by omega`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem mink_term (n p i : ℕ) (hp : 2 ≤ p) :
    n / (p ^ i * (p - 1)) ≤ 2 * n / p ^ (1 + i) := by
  have hpos : 0 < p ^ (1 + i) := Nat.pow_pos (by omega)
  rw [Nat.le_div_iff_mul_le hpos]
  have h1 : n / (p ^ i * (p - 1)) * (p ^ i * (p - 1)) ≤ n := Nat.div_mul_le_self _ _
  have h2 : p ≤ 2 * (p - 1) := by omega
  calc n / (p ^ i * (p - 1)) * p ^ (1 + i)
      = n / (p ^ i * (p - 1)) * p ^ i * p := by rw [pow_add, pow_one]; ring
    _ ≤ n / (p ^ i * (p - 1)) * p ^ i * (2 * (p - 1)) := Nat.mul_le_mul_left _ h2
    _ = 2 * (n / (p ^ i * (p - 1)) * (p ^ i * (p - 1))) := by ring
    _ ≤ 2 * n := Nat.mul_le_mul_left _ h1

/- English proof (translation)
Introduce `n p hp`. Establish `: Fact p.Prime` using `⟨hp⟩`. Establish `hlog : Nat.log p (2 * n) < 2 * n + 2` using `lt_of_le_of_lt (Nat.log_le_self _ _) (by omega)`. Rewrite using `[padicValNat_factorial hlog]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_Ico_eq_sum_range]`. Both sides reduce to the same expression. Use `_ ≤ ∑ i ∈ Ico 1 (2 * n + 2), 2 * n / p ^ i := by`. Apply `Finset.sum_le_sum_of_subset` to reduce the goal to its premises. Apply `Finset.Ico_subset_Ico le_rfl` to reduce the goal to its premises.

Use linear arithmetic over natural numbers and integers.
-/
theorem minkowski_divisor_bound : Minkowski_div := by
  intro n p hp
  have : Fact p.Prime := ⟨hp⟩
  have hlog : Nat.log p (2 * n) < 2 * n + 2 :=
    lt_of_le_of_lt (Nat.log_le_self _ _) (by omega)
  rw [padicValNat_factorial hlog]
  calc ∑ i ∈ range (n + 1), n / (p ^ i * (p - 1))
      ≤ ∑ i ∈ range (n + 1), 2 * n / p ^ (1 + i) :=
        Finset.sum_le_sum (fun i _ => mink_term n p i hp.two_le)
    _ = ∑ i ∈ Ico 1 (n + 2), 2 * n / p ^ i := by
        rw [Finset.sum_Ico_eq_sum_range]; rfl
    _ ≤ ∑ i ∈ Ico 1 (2 * n + 2), 2 * n / p ^ i := by
        apply Finset.sum_le_sum_of_subset
        apply Finset.Ico_subset_Ico le_rfl
        omega

/- English proof (translation)
Use `⟨12, ?_⟩` and prove the remaining obligations. Introduce `M hM`. Establish `hMr : (2 : ℝ) ≤ M` using `by exact_mod_cast hM`. Establish `hM0 : (0 : ℝ) < M` using `by linarith`. Establish `hfac : (((4 * M).factorial : ℕ) : ℝ) ≤ ((4 * M : ℕ) : ℝ) ^ (4 * M)`.

Conclude with `Nat.factorial_le_pow (4 * M)` after adjusting the coercions. Establish `hfpos : (0 : ℝ) < ((4 * M).factorial : ℝ)`. Conclude with `Nat.factorial_pos _` after adjusting the coercions. Establish `h1 : Real.log ((4 * M).factorial : ℝ) ≤ Real.log (((4 * M : ℕ) : ℝ) ^ (4 * M))` using `Real.log_le_log hfpos hfac`. Establish `h2 : Real.log (((4 * M : ℕ) : ℝ) ^ (4 * M)) = (4 * (M : ℝ)) * (Real.log 4 + Real.log M)`.

Rewrite using `[Real.log_pow]`. Use `push_cast`. Rewrite using `[Real.log_mul (by norm_num) hM0.ne']`. Establish `h4 : Real.log 4 = 2 * Real.log 2`. Rewrite using `[show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num`.

Establish `h5 : Real.log 2 ≤ Real.log M` using `Real.log_le_log (by norm_num) hMr`. Establish `h6 : Real.log 4 + Real.log M ≤ 3 * Real.log M` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← h2]`. Conclude with `h1`.

Use `_ ≤ (4 * (M : ℝ)) * (3 * Real.log M) := mul_le_mul_of_nonneg_left h6 (by linarith)`. Use `_ = 12 * M * Real.log M := by ring`.
-/
theorem minkowski_log_bound : Minkowski_log := by
  refine ⟨12, ?_⟩
  intro M hM
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hfac : (((4 * M).factorial : ℕ) : ℝ) ≤ ((4 * M : ℕ) : ℝ) ^ (4 * M) := by
    exact_mod_cast Nat.factorial_le_pow (4 * M)
  have hfpos : (0 : ℝ) < ((4 * M).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have h1 : Real.log ((4 * M).factorial : ℝ) ≤ Real.log (((4 * M : ℕ) : ℝ) ^ (4 * M)) :=
    Real.log_le_log hfpos hfac
  have h2 : Real.log (((4 * M : ℕ) : ℝ) ^ (4 * M)) = (4 * (M : ℝ)) * (Real.log 4 + Real.log M) := by
    rw [Real.log_pow]
    push_cast
    rw [Real.log_mul (by norm_num) hM0.ne']
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h5 : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) hMr
  have h6 : Real.log 4 + Real.log M ≤ 3 * Real.log M := by linarith
  calc Real.log ((4 * M).factorial : ℝ) ≤ (4 * (M : ℝ)) * (Real.log 4 + Real.log M) := by
        rw [← h2]; exact h1
    _ ≤ (4 * (M : ℝ)) * (3 * Real.log M) := mul_le_mul_of_nonneg_left h6 (by linarith)
    _ = 12 * M * Real.log M := by ring

/- English proof (translation)
Introduce `C₀ hC₀`. Use `⟨8 * Real.log C₀ + 31 + C₀, ?_⟩` and prove the remaining obligations. Introduce `f N v T L logg R2 logh hf hN hv hT hL hg hlf hlN hlv hR2 hh`. Establish `hfr : (1 : ℝ) ≤ f` using `by exact_mod_cast hf`. Establish `hNr : (1 : ℝ) ≤ N` using `by exact_mod_cast hN`.

Establish `hc : 0 ≤ Real.log C₀` using `Real.log_nonneg hC₀`. Establish `hlT : 0 ≤ Real.log T` using `Real.log_nonneg hT`. Establish `hC0' : C₀ ≠ 0` using `by positivity`. Establish `hf' : (f : ℝ) ≠ 0` using `by positivity`. Establish `hN' : (N : ℝ) ≠ 0` using `by positivity`.

Establish `hv' : v ≠ 0` using `by positivity`. Establish `hT' : T ≠ 0` using `by positivity`. Establish `hlogR : Real.log R2 = Real.log C₀ + Real.log f + 2 * Real.log N + 2 * Real.log v + 2 * Real.log T`. Rewrite using `[hR2, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul hC0' hf', Real.log_pow, Real.log_pow, Real.log_pow]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hR2' : R2 ≠ 0` using `by rw [hR2]; positivity`. Establish `hlogCR : Real.log (C₀ * R2) = Real.log C₀ + Real.log R2` using `Real.log_mul hC0' hR2'`. Use `set c := Real.log C₀ with hcdef`. Use `set lT := Real.log T with hlTdef`.

Use `set X := L + lT + logg with hX`. Use `clear_value X c lT`. Establish `hX1 : 1 ≤ X` using `by linarith`. Establish `hcX : c ≤ c * X` using `by nlinarith`. Establish `hA : Real.log R2 ≤ (c + 5) * X`.

Establish `: Real.log R2 ≤ c + 5 * X` using `by rw [hlogR]; linarith`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hB : Real.log (C₀ * R2) ≤ (2 * c + 5) * X`. Rewrite using `[hlogCR]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hfN2 : 0 ≤ (f : ℝ) * (N : ℝ) ^ 2` using `by positivity`. Establish `hP : 0 ≤ (f : ℝ) * (N : ℝ) ^ 2 * X` using `by positivity`. Establish `t1 : (N : ℝ) ^ 2 * (2 * f * Real.log (C₀ * R2)) ≤ (f : ℝ) * (N : ℝ) ^ 2 * X * (2 * (2 * c + 5))`. Use `mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ 2 * ((f : ℝ) * (N : ℝ) ^ 2))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `t2 : 4 * f * N * ((N : ℝ) + 1) * (Real.log R2 / 2) ≤ (f : ℝ) * (N : ℝ) ^ 2 * X * (4 * (c + 5))`. Establish `h1 : 4 * f * N * ((N : ℝ) + 1) * (Real.log R2 / 2) ≤ 4 * f * N * ((N : ℝ) + 1) * ((c + 5) * X / 2)` using `mul_le_mul_of_nonneg_left (by linarith) (by positivity)`. Establish `h2 : (N : ℝ) * ((N : ℝ) + 1) ≤ 2 * (N : ℝ) ^ 2` using `by nlinarith`. Establish `h3 : 0 ≤ 2 * (f : ℝ) * ((c + 5) * X)` using `by positivity`. Establish `h4` using `mul_le_mul_of_nonneg_left h2 h3`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `t3 : (f : ℝ) * N * lT ≤ (f : ℝ) * (N : ℝ) ^ 2 * lT`. Establish `h2 : (N : ℝ) ≤ (N : ℝ) ^ 2` using `by nlinarith`. Use `mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ (f : ℝ) * lT)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `t3' : (f : ℝ) * (N : ℝ) ^ 2 * lT ≤ (f : ℝ) * (N : ℝ) ^ 2 * X` using `mul_le_mul_of_nonneg_left (by linarith) hfN2`. Establish `t4 : C₀ * f * (N : ℝ) ^ 2 * logg ≤ (f : ℝ) * (N : ℝ) ^ 2 * X * C₀`. Use `mul_le_mul_of_nonneg_left (by linarith : logg ≤ X) (by positivity : 0 ≤ C₀ * ((f : ℝ) * (N : ℝ) ^ 2))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsum : logh ≤ (f : ℝ) * (N : ℝ) ^ 2 * X * (2 * (2 * c + 5)) + (f : ℝ) * (N : ℝ) ^ 2 * X * (4 * (c + 5)) + ((f : ℝ) * (N : ℝ) ^ 2 * X + (f : ℝ) * (N : ℝ) ^ 2 * X * C₀)` using `by linarith`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem moduli_arithmetic_bound : Ms_arith := by
  intro C₀ hC₀
  refine ⟨8 * Real.log C₀ + 31 + C₀, ?_⟩
  intro f N v T L logg R2 logh hf hN hv hT hL hg hlf hlN hlv hR2 hh
  have hfr : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : 0 ≤ Real.log C₀ := Real.log_nonneg hC₀
  have hlT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hC0' : C₀ ≠ 0 := by positivity
  have hf' : (f : ℝ) ≠ 0 := by positivity
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hv' : v ≠ 0 := by positivity
  have hT' : T ≠ 0 := by positivity
  have hlogR : Real.log R2 = Real.log C₀ + Real.log f + 2 * Real.log N + 2 * Real.log v
      + 2 * Real.log T := by
    rw [hR2, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul hC0' hf', Real.log_pow, Real.log_pow,
      Real.log_pow]
    push_cast; ring
  have hR2' : R2 ≠ 0 := by rw [hR2]; positivity
  have hlogCR : Real.log (C₀ * R2) = Real.log C₀ + Real.log R2 := Real.log_mul hC0' hR2'
  set c := Real.log C₀ with hcdef
  set lT := Real.log T with hlTdef
  set X := L + lT + logg with hX
  clear_value X c lT
  have hX1 : 1 ≤ X := by linarith
  have hcX : c ≤ c * X := by nlinarith
  have hA : Real.log R2 ≤ (c + 5) * X := by
    have : Real.log R2 ≤ c + 5 * X := by rw [hlogR]; linarith
    linarith
  have hB : Real.log (C₀ * R2) ≤ (2 * c + 5) * X := by
    rw [hlogCR]; linarith
  have hfN2 : 0 ≤ (f : ℝ) * (N : ℝ) ^ 2 := by positivity
  have hP : 0 ≤ (f : ℝ) * (N : ℝ) ^ 2 * X := by positivity

  have t1 : (N : ℝ) ^ 2 * (2 * f * Real.log (C₀ * R2)) ≤ (f : ℝ) * (N : ℝ) ^ 2 * X * (2 * (2 * c + 5)) := by
    have := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ 2 * ((f : ℝ) * (N : ℝ) ^ 2))
    linarith

  have t2 : 4 * f * N * ((N : ℝ) + 1) * (Real.log R2 / 2) ≤ (f : ℝ) * (N : ℝ) ^ 2 * X * (4 * (c + 5)) := by
    have h1 : 4 * f * N * ((N : ℝ) + 1) * (Real.log R2 / 2)
        ≤ 4 * f * N * ((N : ℝ) + 1) * ((c + 5) * X / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : (N : ℝ) * ((N : ℝ) + 1) ≤ 2 * (N : ℝ) ^ 2 := by nlinarith
    have h3 : 0 ≤ 2 * (f : ℝ) * ((c + 5) * X) := by positivity
    have h4 := mul_le_mul_of_nonneg_left h2 h3
    linarith

  have t3 : (f : ℝ) * N * lT ≤ (f : ℝ) * (N : ℝ) ^ 2 * lT := by
    have h2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ (f : ℝ) * lT)
    linarith
  have t3' : (f : ℝ) * (N : ℝ) ^ 2 * lT ≤ (f : ℝ) * (N : ℝ) ^ 2 * X :=
    mul_le_mul_of_nonneg_left (by linarith) hfN2
  have t4 : C₀ * f * (N : ℝ) ^ 2 * logg ≤ (f : ℝ) * (N : ℝ) ^ 2 * X * C₀ := by
    have := mul_le_mul_of_nonneg_left (by linarith : logg ≤ X)
      (by positivity : 0 ≤ C₀ * ((f : ℝ) * (N : ℝ) ^ 2))
    linarith
  have hsum : logh ≤ (f : ℝ) * (N : ℝ) ^ 2 * X * (2 * (2 * c + 5)) + (f : ℝ) * (N : ℝ) ^ 2 * X * (4 * (c + 5))
        + ((f : ℝ) * (N : ℝ) ^ 2 * X + (f : ℝ) * (N : ℝ) ^ 2 * X * C₀) := by linarith
  calc logh ≤ (f : ℝ) * (N : ℝ) ^ 2 * X * (2 * (2 * c + 5)) + (f : ℝ) * (N : ℝ) ^ 2 * X * (4 * (c + 5))
        + ((f : ℝ) * (N : ℝ) ^ 2 * X + (f : ℝ) * (N : ℝ) ^ 2 * X * C₀) := hsum
    _ = (8 * c + 31 + C₀) * f * (N : ℝ) ^ 2 * X := by ring

end Formalism.HermitianLattices.TraceIntegrality

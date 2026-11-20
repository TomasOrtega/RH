import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DigammaTendstoLogSubHarmonic

namespace GlobalTheory.CompanionTheory.DigammaBound

open Finset

/- English proof (translation)
Establish `h` using `Complex.abs_re_le_norm (z + (x : ℂ))`. Establish `h2 : (z + (x : ℂ)).re = z.re + x` using `by simp`. Rewrite `h` using `[h2]`. Use `le_abs_self (z.re + x)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma add_half_le_norm (z : ℂ) (hz : 1 / 2 ≤ z.re) (x : ℝ) (hx : 0 ≤ x) :
    x + 1 / 2 ≤ ‖z + (x : ℂ)‖ := by
  have h := Complex.abs_re_le_norm (z + (x : ℂ))
  have h2 : (z + (x : ℂ)).re = z.re + x := by simp
  rw [h2] at h
  have := le_abs_self (z.re + x)
  linarith

/- English proof (translation)
Establish `hk : (0 : ℝ) ≤ (k : ℝ) + 1` using `by positivity`. Establish `hc : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ)` using `by push_cast; rfl`. Establish `hN` using `add_half_le_norm z hz ((k : ℝ) + 1) hk`. Establish `h2 : z + (((k : ℝ) + 1 : ℝ) : ℂ) ≠ 0`. Introduce `h0`.

Rewrite `hN` using `[h0, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : (((k : ℝ) + 1 : ℝ) : ℂ) ≠ 0`. Rewrite using `[← hc]`. Conclude with `Nat.succ_ne_zero k` after adjusting the coercions.

Rewrite using `[hc]`. Establish `: 1 / (((k : ℝ) + 1 : ℝ) : ℂ) - 1 / (z + (((k : ℝ) + 1 : ℝ) : ℂ)) = z / ((((k : ℝ) + 1 : ℝ) : ℂ) * (z + (((k : ℝ) + 1 : ℝ) : ℂ)))`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hk]`.
-/
lemma term_eq (z : ℂ) (hz : 1 / 2 ≤ z.re) (k : ℕ) :
    ‖1 / ((k : ℂ) + 1) - 1 / (z + ((k : ℂ) + 1))‖ =
      ‖z‖ / (((k : ℝ) + 1) * ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have hc : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  have hN := add_half_le_norm z hz ((k : ℝ) + 1) hk
  have h2 : z + (((k : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hN
    linarith
  have h1 : (((k : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
    rw [← hc]
    exact_mod_cast Nat.succ_ne_zero k
  rw [hc]
  have : 1 / (((k : ℝ) + 1 : ℝ) : ℂ) - 1 / (z + (((k : ℝ) + 1 : ℝ) : ℂ)) =
      z / ((((k : ℝ) + 1 : ℝ) : ℂ) * (z + (((k : ℝ) + 1 : ℝ) : ℂ))) := by
    field_simp
    ring
  rw [this, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hk]

/- English proof (translation)
Rewrite using `[term_eq z hz k]`. Establish `ha : (0 : ℝ) < (k : ℝ) + 1` using `by positivity`. Establish `hN` using `add_half_le_norm z hz ((k : ℝ) + 1) ha.le`. Establish `hz' : ‖z‖ ≤ ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖ + ((k : ℝ) + 1)`. Establish `h` using `norm_sub_le (z + (((k : ℝ) + 1 : ℝ) : ℂ)) (((k : ℝ) + 1 : ℝ) : ℂ)`.

Rewrite `h` using `[add_sub_cancel_right, Complex.norm_real, Real.norm_of_nonneg ha.le]`. Conclude with `h`. Establish `hNpos : 0 < ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖` using `by linarith`. Rewrite using `[div_le_iff₀ (by positivity)]`. Establish `: 2 * ((k : ℝ) + 1)⁻¹ * (((k : ℝ) + 1) * ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖) = 2 * ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma term_le_two (z : ℂ) (hz : 1 / 2 ≤ z.re) (k : ℕ) :
    ‖1 / ((k : ℂ) + 1) - 1 / (z + ((k : ℂ) + 1))‖ ≤ 2 * ((k : ℝ) + 1)⁻¹ := by
  rw [term_eq z hz k]
  have ha : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hN := add_half_le_norm z hz ((k : ℝ) + 1) ha.le
  have hz' : ‖z‖ ≤ ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖ + ((k : ℝ) + 1) := by
    have h := norm_sub_le (z + (((k : ℝ) + 1 : ℝ) : ℂ)) (((k : ℝ) + 1 : ℝ) : ℂ)
    rw [add_sub_cancel_right, Complex.norm_real, Real.norm_of_nonneg ha.le] at h
    exact h
  have hNpos : 0 < ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖ := by linarith
  rw [div_le_iff₀ (by positivity)]
  have : 2 * ((k : ℝ) + 1)⁻¹ * (((k : ℝ) + 1) * ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖) =
      2 * ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖ := by
    field_simp
  rw [this]
  linarith

/- English proof (translation)
Rewrite using `[term_eq z hz k]`. Establish `ha : (0 : ℝ) < (k : ℝ) + 1` using `by positivity`. Establish `hN` using `add_half_le_norm z hz ((k : ℝ) + 1) ha.le`. Apply `div_le_div_of_nonneg_left (norm_nonneg z) (by positivity)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma term_le_sq (z : ℂ) (hz : 1 / 2 ≤ z.re) (k : ℕ) :
    ‖1 / ((k : ℂ) + 1) - 1 / (z + ((k : ℂ) + 1))‖ ≤ ‖z‖ / ((k : ℝ) + 1) ^ 2 := by
  rw [term_eq z hz k]
  have ha : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hN := add_half_le_norm z hz ((k : ℝ) + 1) ha.le
  apply div_le_div_of_nonneg_left (norm_nonneg z) (by positivity)
  nlinarith

/- English proof (translation)
Proceed by induction on `n, hn using Nat.le_induction with`. Consider the case `base`. Simplify using `only [sub_self, mul_zero, add_zero, mul_sum]`. Conclude with `sum_le_sum fun i _ => term_le_two z hz i`. Consider the case `succ n hn ih`.

Rewrite using `[sum_range_succ]`. Establish `hn0 : (0 : ℝ) < n` using `by exact_mod_cast (lt_of_lt_of_le hM hn)`. Establish `ht` using `term_le_sq z hz n`. Establish `htel : ‖z‖ / ((n : ℝ) + 1) ^ 2 ≤ ‖z‖ * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))`. Rewrite using `[div_eq_mul_inv]`.

Apply `mul_le_mul_of_nonneg_left _ (norm_nonneg z)` to reduce the goal to its premises. Establish `: 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) = ((n : ℝ) * ((n : ℝ) + 1))⁻¹`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Apply `inv_anti₀ (by positivity)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Use `push_cast`. Use polynomial arithmetic with `[ih, ht, htel]`.
-/
lemma sum_terms_le (z : ℂ) (hz : 1 / 2 ≤ z.re) (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (hn : M ≤ n) :
    ∑ i ∈ range n, ‖1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1))‖ ≤
      2 * ∑ i ∈ range M, ((i : ℝ) + 1)⁻¹ + ‖z‖ * (1 / (M : ℝ) - 1 / (n : ℝ)) := by
  induction n, hn using Nat.le_induction with
  | base =>
    simp only [sub_self, mul_zero, add_zero, mul_sum]
    exact sum_le_sum fun i _ => term_le_two z hz i
  | succ n hn ih =>
    rw [sum_range_succ]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hM hn)
    have ht := term_le_sq z hz n
    have htel : ‖z‖ / ((n : ℝ) + 1) ^ 2 ≤ ‖z‖ * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
      have : 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) = ((n : ℝ) * ((n : ℝ) + 1))⁻¹ := by
        field_simp
        ring
      rw [this]
      apply inv_anti₀ (by positivity)
      nlinarith
    push_cast
    nlinarith [ih, ht, htel]

/- English proof (translation)
Simplify using `[harmonic]`.
-/
lemma harmonic_cast (n : ℕ) : ((harmonic n : ℚ) : ℝ) = ∑ i ∈ range n, ((i : ℝ) + 1)⁻¹ := by
  simp [harmonic]

/- English proof (translation)
Establish `hM0 : (0 : ℝ) < M` using `by exact_mod_cast hM`. Establish `hn1 : 1 ≤ n` using `hM.trans hn`. Establish `hn0 : (0 : ℝ) < n` using `by exact_mod_cast hn1`. Use `set H : ℝ := ∑ i ∈ range n, ((i : ℝ) + 1)⁻¹ with hH`. Establish `hlow : Real.log n ≤ H`.

Establish `h` using `log_add_one_le_harmonic n`. Rewrite `h` using `[harmonic_cast]`. Establish `h2 : Real.log n ≤ Real.log ((n : ℝ) + 1)` using `Real.log_le_log hn0 (by linarith)`. Move the coercions through the operations in `at h`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hup : H ≤ 1 + Real.log n`. Establish `h` using `harmonic_le_one_add_log n`. Rewrite `h` using `[harmonic_cast]`. Conclude with `h`. Establish `hHc : ((H : ℝ) : ℂ) = ∑ i ∈ range n, 1 / ((i : ℂ) + 1)`.

Rewrite using `[hH]`. Use `push_cast`. Simplify using the standard rewrite rules. Establish `hdecomp : ((Real.log n : ℝ) : ℂ) - ∑ k ∈ range (n + 1), 1 / (z + (k : ℂ)) = ((Real.log n - H : ℝ) : ℂ) + ∑ i ∈ range n, (1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1))) - 1 / z`. Rewrite using `[sum_range_succ', sum_sub_distrib, ← hHc]`.

Use `push_cast`. Simplify using `only [add_zero]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : ‖((Real.log n - H : ℝ) : ℂ)‖ ≤ 1`. Rewrite using `[Complex.norm_real, Real.norm_eq_abs, abs_le]`.

Apply the tactic sequence `constructor <;> linarith`. Establish `h2 : ‖∑ i ∈ range n, (1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1)))‖ ≤ 2 * (1 + Real.log M) + 1`. Use `(norm_sum_le _ _).trans ((sum_terms_le z hz M hM n hn).trans ?_)` and prove the remaining obligations. Establish `hHM` using `harmonic_le_one_add_log M`. Rewrite `hHM` using `[harmonic_cast]`.

Establish `h3 : ‖z‖ * (1 / (M : ℝ) - 1 / (n : ℝ)) ≤ 1`. Establish `h4 : ‖z‖ * (1 / (M : ℝ)) ≤ 1`. Rewrite using `[mul_one_div]`. Conclude with `(div_le_one hM0).2 hzM`. Establish `h5 : 0 ≤ ‖z‖ * (1 / (n : ℝ))` using `by positivity`.

Rewrite using `[mul_sub]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : ‖1 / z‖ ≤ 2`. Establish `hzn : 1 / 2 ≤ ‖z‖` using `hz.trans ((le_abs_self _).trans (Complex.abs_re_le_norm z))`.

Rewrite using `[norm_div, norm_one, div_le_iff₀ (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hdecomp]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `norm_add_le _ _`.

Use `_ ≤ 6 + 2 * Real.log M := by linarith`.
-/
lemma partial_le (z : ℂ) (hz : 1 / 2 ≤ z.re) (M : ℕ) (hM : 1 ≤ M) (hzM : ‖z‖ ≤ M)
    (n : ℕ) (hn : M ≤ n) :
    ‖((Real.log n : ℝ) : ℂ) - ∑ k ∈ range (n + 1), 1 / (z + (k : ℂ))‖ ≤
      6 + 2 * Real.log M := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hn1 : 1 ≤ n := hM.trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set H : ℝ := ∑ i ∈ range n, ((i : ℝ) + 1)⁻¹ with hH
  have hlow : Real.log n ≤ H := by
    have h := log_add_one_le_harmonic n
    rw [harmonic_cast] at h
    have h2 : Real.log n ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log hn0 (by linarith)
    push_cast at h
    linarith
  have hup : H ≤ 1 + Real.log n := by
    have h := harmonic_le_one_add_log n
    rw [harmonic_cast] at h
    exact h
  have hHc : ((H : ℝ) : ℂ) = ∑ i ∈ range n, 1 / ((i : ℂ) + 1) := by
    rw [hH]
    push_cast
    simp
  have hdecomp : ((Real.log n : ℝ) : ℂ) - ∑ k ∈ range (n + 1), 1 / (z + (k : ℂ)) =
      ((Real.log n - H : ℝ) : ℂ) +
        ∑ i ∈ range n, (1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1))) - 1 / z := by
    rw [sum_range_succ', sum_sub_distrib, ← hHc]
    push_cast
    simp only [add_zero]
    ring
  have h1 : ‖((Real.log n - H : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have h2 : ‖∑ i ∈ range n, (1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1)))‖ ≤
      2 * (1 + Real.log M) + 1 := by
    refine (norm_sum_le _ _).trans ((sum_terms_le z hz M hM n hn).trans ?_)
    have hHM := harmonic_le_one_add_log M
    rw [harmonic_cast] at hHM
    have h3 : ‖z‖ * (1 / (M : ℝ) - 1 / (n : ℝ)) ≤ 1 := by
      have h4 : ‖z‖ * (1 / (M : ℝ)) ≤ 1 := by
        rw [mul_one_div]
        exact (div_le_one hM0).2 hzM
      have h5 : 0 ≤ ‖z‖ * (1 / (n : ℝ)) := by positivity
      rw [mul_sub]
      linarith
    linarith
  have h3 : ‖1 / z‖ ≤ 2 := by
    have hzn : 1 / 2 ≤ ‖z‖ := hz.trans ((le_abs_self _).trans (Complex.abs_re_le_norm z))
    rw [norm_div, norm_one, div_le_iff₀ (by linarith)]
    linarith
  rw [hdecomp]
  calc _ ≤ ‖((Real.log n - H : ℝ) : ℂ) +
        ∑ i ∈ range n, (1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1)))‖ + ‖1 / z‖ := norm_sub_le _ _
    _ ≤ ‖((Real.log n - H : ℝ) : ℂ)‖ +
        ‖∑ i ∈ range n, (1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1)))‖ + ‖1 / z‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ 6 + 2 * Real.log M := by linarith

/- English proof (translation)
Use `⟨11, by norm_num, fun z hz => ?_⟩` and prove the remaining obligations. Establish `hzn : 1 / 2 ≤ ‖z‖` using `hz.trans ((le_abs_self _).trans (Complex.abs_re_le_norm z))`. Use `set M : ℕ := ⌈‖z‖⌉₊ + 1 with hMdef`. Establish `hM : 1 ≤ M` using `by omega`. Establish `hzM : ‖z‖ ≤ M`.

Rewrite using `[hMdef]`. Use `push_cast`. Combine the linear relations using `[Nat.le_ceil ‖z‖]`. Establish `hMle : (M : ℝ) ≤ ‖z‖ + 2`. Rewrite using `[hMdef]`.

Use `push_cast`. Combine the linear relations using `[Nat.ceil_lt_add_one (norm_nonneg z)]`. Establish `hM0 : (0 : ℝ) < M` using `by exact_mod_cast hM`. Establish `hlogM : Real.log M ≤ Real.log (‖z‖ + 2)` using `Real.log_le_log hM0 hMle`. Establish `hlim` using `(GlobalTheory.CompanionTheory.DigammaLimit.tendsto_log_sub_sum_digamma z (by linarith)).norm`.

Establish `hbd : ‖Complex.digamma z‖ ≤ 6 + 2 * Real.log M` using `le_of_tendsto hlim ((Filter.eventually_ge_atTop M).mono fun n hn => partial_le z hz M hM hzM n hn)`. Establish `hL : (2 : ℝ) / 3 ≤ Real.log (‖z‖ + 2)`. Establish `h2 : Real.log 2 ≤ Real.log (‖z‖ + 2)` using `Real.log_le_log (by norm_num) (by linarith)`. Combine the linear relations using `[Real.log_two_gt_d9]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem digamma_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 / 2 ≤ z.re → ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2) := by
  refine ⟨11, by norm_num, fun z hz => ?_⟩
  have hzn : 1 / 2 ≤ ‖z‖ := hz.trans ((le_abs_self _).trans (Complex.abs_re_le_norm z))
  set M : ℕ := ⌈‖z‖⌉₊ + 1 with hMdef
  have hM : 1 ≤ M := by omega
  have hzM : ‖z‖ ≤ M := by
    rw [hMdef]
    push_cast
    linarith [Nat.le_ceil ‖z‖]
  have hMle : (M : ℝ) ≤ ‖z‖ + 2 := by
    rw [hMdef]
    push_cast
    linarith [Nat.ceil_lt_add_one (norm_nonneg z)]
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hlogM : Real.log M ≤ Real.log (‖z‖ + 2) := Real.log_le_log hM0 hMle
  have hlim := (GlobalTheory.CompanionTheory.DigammaLimit.tendsto_log_sub_sum_digamma z (by linarith)).norm
  have hbd : ‖Complex.digamma z‖ ≤ 6 + 2 * Real.log M :=
    le_of_tendsto hlim ((Filter.eventually_ge_atTop M).mono fun n hn =>
      partial_le z hz M hM hzM n hn)
  have hL : (2 : ℝ) / 3 ≤ Real.log (‖z‖ + 2) := by
    have h2 : Real.log 2 ≤ Real.log (‖z‖ + 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    linarith [Real.log_two_gt_d9]
  linarith

end GlobalTheory.CompanionTheory.DigammaBound

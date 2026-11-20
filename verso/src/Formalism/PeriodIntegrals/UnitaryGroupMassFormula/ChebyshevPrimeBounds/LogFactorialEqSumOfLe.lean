import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PrimeCountBoundOf

noncomputable section

namespace PI.PC

open Finset Real
open ArithmeticFunction hiding log id
open scoped Nat Chebyshev ArithmeticFunction.zeta

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Finset.sum_Ioc_succ_top (Nat.zero_le n), ← ih, Nat.factorial_succ, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_factorial_eq_sum_log (N : ℕ) : log ((N ! : ℕ) : ℝ) = ∑ m ∈ Ioc 0 N, log (m : ℝ) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le n), ← ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))]
    push_cast
    ring

/- English proof (translation)
Rewrite using `[log_factorial_eq_sum_log]`. Establish `h1 : ∀ m ∈ Ioc 0 N, log (m : ℝ) = ∑ d ∈ Ioc 0 N, if d ∣ m then Λ d else 0`. Introduce `m hm`. Rewrite `hm` using `[Finset.mem_Ioc]`. Rewrite using `[← Finset.sum_filter, ← ArithmeticFunction.vonMangoldt_sum]`.

Apply `Finset.sum_congr _ (fun _ _ => rfl)` to reduce the goal to its premises. Use extensionality with `d`. Simplify using `only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hd, -⟩`.

Conclude with `⟨⟨Nat.pos_of_dvd_of_pos hd hm.1, (Nat.le_of_dvd hm.1 hd).trans hm.2⟩, hd⟩`. Introduce and unpack `⟨-, hd⟩`. Conclude with `⟨hd, by omega⟩`. Rewrite using `[Finset.sum_congr rfl h1, Finset.sum_comm]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `d _`. Rewrite using `[← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_factorial_eq_sum (N : ℕ) :
    log ((N ! : ℕ) : ℝ) = ∑ d ∈ Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ) := by
  rw [log_factorial_eq_sum_log]
  have h1 : ∀ m ∈ Ioc 0 N, log (m : ℝ) = ∑ d ∈ Ioc 0 N, if d ∣ m then Λ d else 0 := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    rw [← Finset.sum_filter, ← ArithmeticFunction.vonMangoldt_sum]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors]
    constructor
    · rintro ⟨hd, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hm.1, (Nat.le_of_dvd hm.1 hd).trans hm.2⟩, hd⟩
    · rintro ⟨-, hd⟩
      exact ⟨hd, by omega⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div]
  ring

/- English proof (translation)
Rewrite using `[log_factorial_eq_sum]`. Apply `Finset.sum_subset (Finset.Ioc_subset_Ioc_right h)` to reduce the goal to its premises. Introduce `d hdM hd`. Establish `hd0 : 0 < d` using `(Finset.mem_Ioc.mp hdM).1`. Establish `hNd : N < d`.

Assume the negation of the conclusion as `hc`. Conclude with `hd (Finset.mem_Ioc.mpr ⟨hd0, by omega⟩)`. Rewrite using `[Nat.div_eq_of_lt hNd]`. Simplify using the standard rewrite rules.
-/
theorem log_factorial_eq_sum_of_le {N M : ℕ} (h : N ≤ M) :
    log ((N ! : ℕ) : ℝ) = ∑ d ∈ Ioc 0 M, Λ d * ((N / d : ℕ) : ℝ) := by
  rw [log_factorial_eq_sum]
  apply Finset.sum_subset (Finset.Ioc_subset_Ioc_right h)
  intro d hdM hd
  have hd0 : 0 < d := (Finset.mem_Ioc.mp hdM).1
  have hNd : N < d := by
    by_contra hc
    exact hd (Finset.mem_Ioc.mpr ⟨hd0, by omega⟩)
  rw [Nat.div_eq_of_lt hNd]
  simp

def chE (q : ℕ) : ℝ :=
  (q : ℝ) - ((q / 2 : ℕ) : ℝ) - ((q / 3 : ℕ) : ℝ) - ((q / 5 : ℕ) : ℝ) + ((q / 30 : ℕ) : ℝ)

/- English proof (translation)
Establish `h : q / 2 + q / 3 + q / 5 ≤ q + q / 30` using `by omega`. Establish `h' : ((q / 2 : ℕ) : ℝ) + ((q / 3 : ℕ) : ℝ) + ((q / 5 : ℕ) : ℝ) ≤ (q : ℝ) + ((q / 30 : ℕ) : ℝ)`. Conclude with `h` after adjusting the coercions. Unfold `chE`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem chE_nonneg (q : ℕ) : 0 ≤ chE q := by
  have h : q / 2 + q / 3 + q / 5 ≤ q + q / 30 := by omega
  have h' : ((q / 2 : ℕ) : ℝ) + ((q / 3 : ℕ) : ℝ) + ((q / 5 : ℕ) : ℝ) ≤ (q : ℝ) + ((q / 30 : ℕ) : ℝ) := by
    exact_mod_cast h
  unfold chE
  linarith

/- English proof (translation)
Establish `h : q + q / 30 ≤ q / 2 + q / 3 + q / 5 + 1` using `by omega`. Establish `h' : (q : ℝ) + ((q / 30 : ℕ) : ℝ) ≤ ((q / 2 : ℕ) : ℝ) + ((q / 3 : ℕ) : ℝ) + ((q / 5 : ℕ) : ℝ) + 1`. Conclude with `h` after adjusting the coercions. Unfold `chE`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem chE_le_one (q : ℕ) : chE q ≤ 1 := by
  have h : q + q / 30 ≤ q / 2 + q / 3 + q / 5 + 1 := by omega
  have h' : (q : ℝ) + ((q / 30 : ℕ) : ℝ) ≤ ((q / 2 : ℕ) : ℝ) + ((q / 3 : ℕ) : ℝ) + ((q / 5 : ℕ) : ℝ) + 1 := by
    exact_mod_cast h
  unfold chE
  linarith

/- English proof (translation)
Establish `h : q / 2 + q / 3 + q / 5 + 1 = q + q / 30` using `by omega`. Establish `h' : ((q / 2 : ℕ) : ℝ) + ((q / 3 : ℕ) : ℝ) + ((q / 5 : ℕ) : ℝ) + 1 = (q : ℝ) + ((q / 30 : ℕ) : ℝ)`. Conclude with `h` after adjusting the coercions. Unfold `chE`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem chE_eq_one {q : ℕ} (h1 : 1 ≤ q) (h6 : q < 6) : chE q = 1 := by
  have h : q / 2 + q / 3 + q / 5 + 1 = q + q / 30 := by omega
  have h' : ((q / 2 : ℕ) : ℝ) + ((q / 3 : ℕ) : ℝ) + ((q / 5 : ℕ) : ℝ) + 1 = (q : ℝ) + ((q / 30 : ℕ) : ℝ) := by
    exact_mod_cast h
  unfold chE
  linarith

/- English proof (translation)
The claim follows from `Nat.floor_div_natCast x k`.
-/
private theorem nat_floor_div_natCast (x : ℝ) (k : ℕ) : ⌊x / (k : ℝ)⌋₊ = ⌊x⌋₊ / k :=
  Nat.floor_div_natCast x k

/- English proof (translation)
Establish `hL : ∀ k : ℕ, lf (x / (k : ℝ)) = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (((⌊x⌋₊ / d) / k : ℕ) : ℝ)`. Introduce `k`. Unfold `lf`. Rewrite using `[nat_floor_div_natCast, log_factorial_eq_sum_of_le (Nat.div_le_self ⌊x⌋₊ k)]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `d _`. Rewrite using `[Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm k d]`. Establish `h1 : lf x = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ((⌊x⌋₊ / d : ℕ) : ℝ)`. Unfold `lf`. Conclude with `log_factorial_eq_sum _`.

Establish `h2` using `hL 2`. Establish `h3` using `hL 3`. Establish `h5` using `hL 5`. Establish `h30` using `hL 30`. Move the coercions through the operations in `at h2 h3 h5 h30`.

Unfold `chD`. Rewrite using `[h1, h2, h3, h5, h30]`. Rewrite using `[← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `d _`.

Unfold `chE`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chD_eq_sum (x : ℝ) : chD x = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * chE (⌊x⌋₊ / d) := by
  have hL : ∀ k : ℕ, lf (x / (k : ℝ)) =
      ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (((⌊x⌋₊ / d) / k : ℕ) : ℝ) := by
    intro k
    unfold lf
    rw [nat_floor_div_natCast, log_factorial_eq_sum_of_le (Nat.div_le_self ⌊x⌋₊ k)]
    apply Finset.sum_congr rfl
    intro d _
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm k d]
  have h1 : lf x = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ((⌊x⌋₊ / d : ℕ) : ℝ) := by
    unfold lf
    exact log_factorial_eq_sum _
  have h2 := hL 2
  have h3 := hL 3
  have h5 := hL 5
  have h30 := hL 30
  push_cast at h2 h3 h5 h30
  unfold chD
  rw [h1, h2, h3, h5, h30]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  unfold chE
  ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem chebyshev_psi_eq_sum_Ioc_vonMangoldt (x : ℝ) : ψ x = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n := by
  rfl

/- English proof (translation)
Rewrite using `[chD_eq_sum, chebyshev_psi_eq_sum_Ioc_vonMangoldt]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `d _`. Establish `hc` using `chE_le_one (⌊x⌋₊ / d)`. Establish `h0 : 0 ≤ Λ d` using `ArithmeticFunction.vonMangoldt_nonneg`.

Conclude with `mul_le_of_le_one_right h0 hc`.
-/
theorem chD_le_psi (x : ℝ) : chD x ≤ ψ x := by
  rw [chD_eq_sum, chebyshev_psi_eq_sum_Ioc_vonMangoldt]
  apply Finset.sum_le_sum
  intro d _
  have hc := chE_le_one (⌊x⌋₊ / d)
  have h0 : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
  exact mul_le_of_le_one_right h0 hc

/- English proof (translation)
Rewrite using `[Finset.sum_Ioc_consecutive f (Nat.zero_le (N / 6)) (Nat.div_le_self N 6)]`.
-/
private theorem sum_Ioc_eq_sum_Ioc_div_six_add_sum_Ioc (N : ℕ) (f : ℕ → ℝ) :
    ∑ d ∈ Ioc 0 N, f d = ∑ d ∈ Ioc 0 (N / 6), f d + ∑ d ∈ Ioc (N / 6) N, f d := by
  rw [Finset.sum_Ioc_consecutive f (Nat.zero_le (N / 6)) (Nat.div_le_self N 6)]

/- English proof (translation)
Establish `h6 : ⌊x / 6⌋₊ = ⌊x⌋₊ / 6`. Simplify using `using nat_floor_div_natCast x 6`. Rewrite using `[chebyshev_psi_eq_sum_Ioc_vonMangoldt, chebyshev_psi_eq_sum_Ioc_vonMangoldt, h6, chD_eq_sum, sum_Ioc_eq_sum_Ioc_div_six_add_sum_Ioc ⌊x⌋₊ (fun d => Λ d), sum_Ioc_eq_sum_Ioc_div_six_add_sum_Ioc ⌊x⌋₊ (fun d => Λ d * chE (⌊x⌋₊ / d))]`. Establish `hA : 0 ≤ ∑ d ∈ Ioc 0 (⌊x⌋₊ / 6), Λ d * chE (⌊x⌋₊ / d)` using `Finset.sum_nonneg fun d _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (chE_nonneg _)`. Establish `hB : ∑ d ∈ Ioc (⌊x⌋₊ / 6) ⌊x⌋₊, Λ d ≤ ∑ d ∈ Ioc (⌊x⌋₊ / 6) ⌊x⌋₊, Λ d * chE (⌊x⌋₊ / d)`.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `d hd`. Rewrite `hd` using `[Finset.mem_Ioc]`. Establish `hd0 : 0 < d` using `by omega`. Establish `hq1 : 1 ≤ ⌊x⌋₊ / d` using `Nat.div_pos hd.2 hd0`.

Establish `hq6 : ⌊x⌋₊ / d < 6`. Conclude with `Nat.div_lt_of_lt_mul (by omega)`. Rewrite using `[chE_eq_one hq1 hq6, mul_one]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem psi_sub_psi_le_chD (x : ℝ) : ψ x - ψ (x / 6) ≤ chD x := by
  have h6 : ⌊x / 6⌋₊ = ⌊x⌋₊ / 6 := by
    simpa using nat_floor_div_natCast x 6
  rw [chebyshev_psi_eq_sum_Ioc_vonMangoldt, chebyshev_psi_eq_sum_Ioc_vonMangoldt, h6, chD_eq_sum,
    sum_Ioc_eq_sum_Ioc_div_six_add_sum_Ioc ⌊x⌋₊ (fun d => Λ d),
    sum_Ioc_eq_sum_Ioc_div_six_add_sum_Ioc ⌊x⌋₊ (fun d => Λ d * chE (⌊x⌋₊ / d))]
  have hA : 0 ≤ ∑ d ∈ Ioc 0 (⌊x⌋₊ / 6), Λ d * chE (⌊x⌋₊ / d) :=
    Finset.sum_nonneg fun d _ =>
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (chE_nonneg _)
  have hB : ∑ d ∈ Ioc (⌊x⌋₊ / 6) ⌊x⌋₊, Λ d ≤
      ∑ d ∈ Ioc (⌊x⌋₊ / 6) ⌊x⌋₊, Λ d * chE (⌊x⌋₊ / d) := by
    apply Finset.sum_le_sum
    intro d hd
    rw [Finset.mem_Ioc] at hd
    have hd0 : 0 < d := by omega
    have hq1 : 1 ≤ ⌊x⌋₊ / d := Nat.div_pos hd.2 hd0
    have hq6 : ⌊x⌋₊ / d < 6 := by
      exact Nat.div_lt_of_lt_mul (by omega)
    rw [chE_eq_one hq1 hq6, mul_one]
  linarith

/- English proof (translation)
Introduce `x _` and use `⟨psi_sub_psi_le_chD x, chD_le_psi x⟩`.
-/
theorem sandwich : Sandwich := fun x _ => ⟨psi_sub_psi_le_chD x, chD_le_psi x⟩

end PI.PC

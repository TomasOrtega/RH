import Mathlib
open Complex Filter Topology

namespace GlobalTheory

/- English proof (translation)
Break down `eq_or_ne d 0 with rfl | hd` into its components or cases. Simplify using the standard rewrite rules. Establish `hd' : (d : ℂ) ≠ 0` using `by exact_mod_cast hd`. Rewrite using `[LSeries.term_of_ne_zero (mul_ne_zero hd hd), LSeries.term_of_ne_zero hd]`. Simplify using `only [Nat.sqrt_eq, if_true]`.

Rewrite using `[Nat.cast_mul, natCast_mul_natCast_cpow, ← cpow_add _ _ hd', ← cpow_natCast, mul_div_assoc, ← cpow_sub _ _ hd', div_eq_mul_inv, ← cpow_neg]`. Use `congr 2`. Establish `h3 : 1 ≤ 3 * e` using `by omega`. Move the coercions through the operations in `[Nat.cast_sub h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lseriesSquares_term (e : ℕ) (c : ℕ → ℂ) (s : ℝ) (he : 1 ≤ e) (d : ℕ) :
    LSeries.term (fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then
        c (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0) (((2 * (e : ℝ) + s : ℝ)) : ℂ) (d * d)
      = LSeries.term c ((e + 1 : ℕ) + 2 * s) d := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  rw [LSeries.term_of_ne_zero (mul_ne_zero hd hd), LSeries.term_of_ne_zero hd]
  simp only [Nat.sqrt_eq, if_true]
  rw [Nat.cast_mul, natCast_mul_natCast_cpow, ← cpow_add _ _ hd', ← cpow_natCast, mul_div_assoc,
    ← cpow_sub _ _ hd', div_eq_mul_inv, ← cpow_neg]
  congr 2
  have h3 : 1 ≤ 3 * e := by omega
  push_cast [Nat.cast_sub h3]
  ring

/- English proof (translation)
Introduce `e χ ψ θ s he hs hb`. Establish `hinj : Function.Injective (fun d : ℕ => d * d)` using `fun a b h => Nat.mul_self_inj.mp h`. Establish `hterm` using `lseriesSquares_term e (fun n => χ n * ψ n * θ n) s he`. Use `set f : ℕ → ℂ := fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then χ (Nat.sqrt n) * ψ (Nat.sqrt n) * θ (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0 with hf`. Establish `hzero : ∀ n, n ∉ Set.range (fun d : ℕ => d * d) → LSeries.term f (((2 * (e : ℝ) + s : ℝ)) : ℂ) n = 0`.

Introduce `n hn`. Establish `hn' : ¬ (Nat.sqrt n * Nat.sqrt n = n)` using `fun h => hn ⟨_, h⟩`. Rewrite using `[LSeries.term_def]`. Use `split_ifs`. Both sides reduce to the same expression.

Simplify using `[hf, hn']`. Establish `hsum : LSeriesSummable (fun n => χ n * ψ n * θ n) ((e + 1 : ℕ) + 2 * s)`. Use `LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => ?_) ?_` and prove the remaining obligations. Take `⟨h1, h2, h3⟩` from `hb n`. Rewrite using `[norm_mul, norm_mul]`.

Conclude with `mul_le_one₀ (mul_le_one₀ h1 (norm_nonneg _) h2) (norm_nonneg _) h3`. Establish `: (0 : ℝ) ≤ e` using `Nat.cast_nonneg e`. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Prove the components needed by the constructor for the conclusion.

Use `(hinj.summable_iff hzero).mp ?_` and prove the remaining obligations. Conclude with `(show Summable _ from hsum).congr fun d => (hterm d).symm`. Unfold `LSeries`. Rewrite using `[← hinj.tsum_eq (fun n hn => by`. Assume the negation of the conclusion as `h`.

Conclude with `hn (hzero n h))]`. Conclude with `tsum_congr hterm`.
-/
theorem lseriesSquares_eq : ∀ (e : ℕ) (χ ψ θ : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖χ n‖ ≤ 1 ∧ ‖ψ n‖ ≤ 1 ∧ ‖θ n‖ ≤ 1) → LSeriesSummable (fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then χ (Nat.sqrt n) * ψ (Nat.sqrt n) * θ (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0) (((2 * (e : ℝ) + s : ℝ)) : ℂ) ∧ LSeries (fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then χ (Nat.sqrt n) * ψ (Nat.sqrt n) * θ (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0) (((2 * (e : ℝ) + s : ℝ)) : ℂ) = LSeries (fun n => χ n * ψ n * θ n) ((e + 1 : ℕ) + 2 * s) := by
  intro e χ ψ θ s he hs hb
  have hinj : Function.Injective (fun d : ℕ => d * d) := fun a b h => Nat.mul_self_inj.mp h
  have hterm := lseriesSquares_term e (fun n => χ n * ψ n * θ n) s he
  set f : ℕ → ℂ := fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then
    χ (Nat.sqrt n) * ψ (Nat.sqrt n) * θ (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0 with hf
  have hzero : ∀ n, n ∉ Set.range (fun d : ℕ => d * d) →
      LSeries.term f (((2 * (e : ℝ) + s : ℝ)) : ℂ) n = 0 := by
    intro n hn
    have hn' : ¬ (Nat.sqrt n * Nat.sqrt n = n) := fun h => hn ⟨_, h⟩
    rw [LSeries.term_def]
    split_ifs
    · rfl
    · simp [hf, hn']
  have hsum : LSeriesSummable (fun n => χ n * ψ n * θ n) ((e + 1 : ℕ) + 2 * s) := by
    refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => ?_) ?_
    · obtain ⟨h1, h2, h3⟩ := hb n
      rw [norm_mul, norm_mul]
      exact mul_le_one₀ (mul_le_one₀ h1 (norm_nonneg _) h2) (norm_nonneg _) h3
    · have : (0 : ℝ) ≤ e := Nat.cast_nonneg e
      simp
      linarith
  constructor
  · refine (hinj.summable_iff hzero).mp ?_
    exact (show Summable _ from hsum).congr fun d => (hterm d).symm
  · unfold LSeries
    rw [← hinj.tsum_eq (fun n hn => by
      by_contra h
      exact hn (hzero n h))]
    exact tsum_congr hterm

end GlobalTheory

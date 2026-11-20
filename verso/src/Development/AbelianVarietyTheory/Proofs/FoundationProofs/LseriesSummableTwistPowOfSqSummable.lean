import Mathlib
open Complex Filter Topology

namespace GlobalTheory

/- English proof (translation)
Introduce `e ψ g s he hs hψ hg`. Establish `h1` using `hg s hs`. Establish `h2 : Summable fun n : ℕ => 1 / (n : ℝ) ^ (1 + s)` using `Real.summable_one_div_nat_rpow.mpr (by linarith)`. Use `Summable.of_norm_bounded (h1.add h2) fun n => ?_` and prove the remaining obligations. Rewrite using `[LSeries.norm_term_eq]`.

Use `split_ifs with hn`. Check the signs of the components of the expression. Establish `hx : (0 : ℝ) < n` using `by exact_mod_cast Nat.pos_of_ne_zero hn`. Take `⟨k, rfl⟩ : ∃ k, e = k + 1` from `⟨e - 1, by omega⟩`. Simplify using `only [Complex.ofReal_re, norm_mul, norm_pow, Complex.norm_natCast, Nat.add_sub_cancel]`.

Use `set x : ℝ := (n : ℝ) with hxdef`. Use `set A : ℝ := ‖g n‖ with hA`. Establish `hA0 : 0 ≤ A` using `norm_nonneg _`. Use `set p : ℝ := x ^ (-(2 * (k : ℝ) + 3 + s) / 2) with hp`. Use `set q : ℝ := x ^ (-(1 + s) / 2) with hq`.

Establish `hp0 : 0 ≤ p` using `by positivity`. Establish `hq0 : 0 ≤ q` using `by positivity`. Establish `e1 : A ^ 2 / x ^ (((2 * (k + 1) + 1 : ℕ) : ℝ) + s) = (A * p) ^ 2`. Rewrite using `[mul_pow, hp, ← Real.rpow_natCast (x ^ _) 2, ← Real.rpow_mul hx.le, div_eq_mul_inv, ← Real.rpow_neg hx.le]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : 1 / x ^ (1 + s) = q ^ 2`. Rewrite using `[hq, ← Real.rpow_natCast (x ^ _) 2, ← Real.rpow_mul hx.le, one_div, ← Real.rpow_neg hx.le]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e3 : x ^ k / x ^ (2 * ((k + 1 : ℕ) : ℝ) + s) = p * q`. Rewrite using `[hp, hq, ← Real.rpow_natCast x k, ← Real.rpow_sub hx, ← Real.rpow_add hx]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2]`. Establish `e4 : ‖ψ n‖ * x ^ k * A / x ^ (2 * ((k + 1 : ℕ) : ℝ) + s) = ‖ψ n‖ * (A * p * q)`. Rewrite using `[mul_assoc A, ← e3]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e4]`. Establish `h3 : ‖ψ n‖ * (A * p * q) ≤ A * p * q` using `mul_le_of_le_one_left (by positivity) (hψ n)`. Establish `h4 : 0 ≤ A * p * q` using `by positivity`. Use polynomial arithmetic with `[sq_nonneg (A * p - q)]`.
-/
theorem lseriesSummable_twist_pow_of_sq_summable :
    ∀ (e : ℕ) (ψ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖ψ n‖ ≤ 1) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → LSeriesSummable (fun n : ℕ => ψ n * (n : ℂ) ^ (e - 1) * g n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) := by
  intro e ψ g s he hs hψ hg
  have h1 := hg s hs
  have h2 : Summable fun n : ℕ => 1 / (n : ℝ) ^ (1 + s) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  refine Summable.of_norm_bounded (h1.add h2) fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  · have hx : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    simp only [Complex.ofReal_re, norm_mul, norm_pow, Complex.norm_natCast, Nat.add_sub_cancel]
    set x : ℝ := (n : ℝ) with hxdef
    set A : ℝ := ‖g n‖ with hA
    have hA0 : 0 ≤ A := norm_nonneg _
    set p : ℝ := x ^ (-(2 * (k : ℝ) + 3 + s) / 2) with hp
    set q : ℝ := x ^ (-(1 + s) / 2) with hq
    have hp0 : 0 ≤ p := by positivity
    have hq0 : 0 ≤ q := by positivity
    have e1 : A ^ 2 / x ^ (((2 * (k + 1) + 1 : ℕ) : ℝ) + s) = (A * p) ^ 2 := by
      rw [mul_pow, hp, ← Real.rpow_natCast (x ^ _) 2, ← Real.rpow_mul hx.le, div_eq_mul_inv,
        ← Real.rpow_neg hx.le]
      congr 2
      push_cast
      ring
    have e2 : 1 / x ^ (1 + s) = q ^ 2 := by
      rw [hq, ← Real.rpow_natCast (x ^ _) 2, ← Real.rpow_mul hx.le, one_div,
        ← Real.rpow_neg hx.le]
      congr 1
      push_cast
      ring
    have e3 : x ^ k / x ^ (2 * ((k + 1 : ℕ) : ℝ) + s) = p * q := by
      rw [hp, hq, ← Real.rpow_natCast x k, ← Real.rpow_sub hx, ← Real.rpow_add hx]
      congr 1
      push_cast
      ring
    rw [e1, e2]
    have e4 : ‖ψ n‖ * x ^ k * A / x ^ (2 * ((k + 1 : ℕ) : ℝ) + s) = ‖ψ n‖ * (A * p * q) := by
      rw [mul_assoc A, ← e3]; ring
    rw [e4]
    have h3 : ‖ψ n‖ * (A * p * q) ≤ A * p * q :=
      mul_le_of_le_one_left (by positivity) (hψ n)
    have h4 : 0 ≤ A * p * q := by positivity
    nlinarith [sq_nonneg (A * p - q)]

end GlobalTheory

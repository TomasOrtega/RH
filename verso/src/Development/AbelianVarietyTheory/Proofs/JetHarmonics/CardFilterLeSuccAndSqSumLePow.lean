import Mathlib
open Finset
open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Introduce `n kk bv h1 h2 h3`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hlt : kk - 1 < n` using `by omega`. Establish `: (univ.filter fun a : Fin n => kk ≤ a.val + 1) = Finset.Ici (⟨kk - 1, hlt⟩ : Fin n)`. Use extensionality with `a`.

Simplify using `only [mem_filter, mem_univ, true_and, Finset.mem_Ici, Fin.le_def]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[this, Fin.card_Ici]`. Simplify using `only`. Use linear arithmetic over natural numbers and integers.

Establish `e1 : n + 1 - kk = (n - kk) + 1` using `by omega`. Establish `hn2 : (2 : ℝ) ≤ n` using `by exact_mod_cast (by omega : 2 ≤ n)`. Establish `hM : ((n + 1 - kk : ℕ) : ℝ) ≤ n` using `by exact_mod_cast (by omega : n + 1 - kk ≤ n)`. Establish `hb : (2 : ℝ) ≤ bv` using `hn2.trans h3`. Establish `hX : (1 : ℝ) ≤ (6 * bv) ^ (n - kk)` using `one_le_pow₀ (by linarith)`.

Establish `e2 : (6 * bv) ^ (2 * (n + 1 - kk)) = 36 * bv ^ 2 * ((6 * bv) ^ (n - kk)) ^ 2`. Rewrite using `[e1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Use `set X := (6 * bv) ^ (n - kk)`.

Use `set c := ((n + 1 - kk : ℕ) : ℝ)`. Establish `hX2 : (1 : ℝ) ≤ X ^ 2` using `one_le_pow₀ hX`. Establish `hc : c ≤ bv` using `hM.trans h3`. Establish `h4 : c * X ^ 2 ≤ bv * X ^ 2` using `mul_le_mul_of_nonneg_right hc (by positivity)`. Establish `h5 : (9 * bv + 2) * X ^ 2 ≤ 36 * bv ^ 2 * X ^ 2` using `mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem card_filter_le_succ_and_sq_sum_le_pow : ∀ (n kk : ℕ) (bv : ℝ), 1 ≤ kk → kk + 1 ≤ n → (n : ℝ) ≤ bv → (univ.filter fun a : Fin n => kk ≤ a.val + 1).card = n + 1 - kk ∧ (18 / 13 : ℝ) ^ 2 + ((n + 1 - kk : ℕ) : ℝ) * (3 * (6 * bv) ^ (n - kk)) ^ 2 ≤ (6 * bv) ^ (2 * (n + 1 - kk)) := by
  intro n kk bv h1 h2 h3
  refine ⟨?_, ?_⟩
  · have hlt : kk - 1 < n := by omega
    have : (univ.filter fun a : Fin n => kk ≤ a.val + 1) = Finset.Ici (⟨kk - 1, hlt⟩ : Fin n) := by
      ext a
      simp only [mem_filter, mem_univ, true_and, Finset.mem_Ici, Fin.le_def]
      omega
    rw [this, Fin.card_Ici]
    simp only
    omega
  · have e1 : n + 1 - kk = (n - kk) + 1 := by omega
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
    have hM : ((n + 1 - kk : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : n + 1 - kk ≤ n)
    have hb : (2 : ℝ) ≤ bv := hn2.trans h3
    have hX : (1 : ℝ) ≤ (6 * bv) ^ (n - kk) := one_le_pow₀ (by linarith)
    have e2 : (6 * bv) ^ (2 * (n + 1 - kk)) = 36 * bv ^ 2 * ((6 * bv) ^ (n - kk)) ^ 2 := by
      rw [e1]; ring
    rw [e2]
    set X := (6 * bv) ^ (n - kk)
    set c := ((n + 1 - kk : ℕ) : ℝ)
    have hX2 : (1 : ℝ) ≤ X ^ 2 := one_le_pow₀ hX
    have hc : c ≤ bv := hM.trans h3
    have h4 : c * X ^ 2 ≤ bv * X ^ 2 := mul_le_mul_of_nonneg_right hc (by positivity)
    have h5 : (9 * bv + 2) * X ^ 2 ≤ 36 * bv ^ 2 * X ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    nlinarith

end GlobalTheory

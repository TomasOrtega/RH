import Mathlib
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Introduce `p j hp`. Establish `hp' : (2 : ℝ) ≤ p` using `by exact_mod_cast hp`. Establish `h0 : (p : ℝ) ≠ 0` using `by positivity`. Establish `h1 : (p : ℝ) - 1 ≠ 0` using `by linarith`. Establish `hr : 1 / (p : ℝ) < 1` using `by rw [div_lt_one (by linarith)]; linarith`.

Establish `hs` using `(hasSum_geometric_of_lt_one (by positivity) hr).mul_left ((j : ℝ) / p)`. Establish `hf : (fun n : ℕ => (j : ℝ) / (p : ℝ) ^ (n + 1)) = fun n : ℕ => (j : ℝ) / p * (1 / (p : ℝ)) ^ n`. Use function extensionality and compare the values at `n`. Rewrite using `[one_div_pow, pow_succ]`. Clear the denominators using the available nonvanishing facts.

Establish `hv : (j : ℝ) / ((p : ℝ) - 1) = (j : ℝ) / p * (1 - 1 / (p : ℝ))⁻¹`. Rewrite using `[one_sub_div h0, inv_div]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hf, hv]`. Conclude with `hs`.
-/
theorem ep_split : ∀ (p j : ℕ), 2 ≤ p →
    HasSum (fun n : ℕ => (j : ℝ) / (p : ℝ) ^ (n + 1)) ((j : ℝ) / ((p : ℝ) - 1)) := by
  intro p j hp
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h0 : (p : ℝ) ≠ 0 := by positivity
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hr : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hs := (hasSum_geometric_of_lt_one (by positivity) hr).mul_left ((j : ℝ) / p)
  have hf : (fun n : ℕ => (j : ℝ) / (p : ℝ) ^ (n + 1)) =
      fun n : ℕ => (j : ℝ) / p * (1 / (p : ℝ)) ^ n := by
    funext n
    rw [one_div_pow, pow_succ]
    field_simp
  have hv : (j : ℝ) / ((p : ℝ) - 1) = (j : ℝ) / p * (1 - 1 / (p : ℝ))⁻¹ := by
    rw [one_sub_div h0, inv_div]
    field_simp
  rw [hf, hv]
  exact hs

end GlobalTheory.CompanionTheory.Ar.Flat

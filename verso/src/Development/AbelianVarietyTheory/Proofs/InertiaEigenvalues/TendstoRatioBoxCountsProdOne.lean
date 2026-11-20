import Mathlib
open Filter

namespace GlobalTheory

/- English proof (translation)
Establish `key : ∀ i, Tendsto (fun k : ℕ => ((2 * (k + m) * c i + 1 : ℕ) : ℝ) / ((2 * k * c i + 1 : ℕ) : ℝ)) atTop (nhds 1)`. Introduce `i`. Break down `Nat.eq_zero_or_pos (c i) with h | h` into its components or cases. Simplify using `[h]`. Establish `hc : (0:ℝ) < c i` using `by exact_mod_cast h`.

Establish `hden : Tendsto (fun k : ℕ => ((2 * k * c i + 1 : ℕ) : ℝ)) atTop atTop`. Use `push_cast`. Apply `tendsto_atTop_add_const_right` to reduce the goal to its premises. Conclude with `(tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ) < 2)).atTop_mul_const hc`. Establish `h0 : Tendsto (fun k : ℕ => (2 * m * c i : ℝ) / ((2 * k * c i + 1 : ℕ) : ℝ)) atTop (nhds 0)` using `tendsto_const_nhds.div_atTop hden`.

Establish `h1` using `(tendsto_const_nhds (x := (1:ℝ))).add h0`. Rewrite `h1` using `[add_zero]`. Use `h1.congr (fun k => ?_)` and prove the remaining obligations. Establish `hpos : ((2 * k * c i + 1 : ℕ) : ℝ) ≠ 0` using `by positivity`. Clear the denominators using the available nonvanishing facts.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h` using `tendsto_finset_prod (Finset.univ : Finset (Fin r)) (fun i _ => key i)`. Simplify using `only [Finset.prod_const_one] at h`. Use `h.congr (fun k => ?_)` and prove the remaining obligations.

Rewrite using `[Nat.cast_prod, Nat.cast_prod, Finset.prod_div_distrib]`.
-/
theorem ratio_box_counts_tendsto_one (r : ℕ) (c : Fin r → ℕ) (m : ℕ) :
    Filter.Tendsto (fun k : ℕ => ((∏ i, (2 * (k + m) * c i + 1) : ℕ) : ℝ) /
      ((∏ i, (2 * k * c i + 1) : ℕ) : ℝ)) Filter.atTop (nhds 1) := by
  have key : ∀ i, Tendsto (fun k : ℕ => ((2 * (k + m) * c i + 1 : ℕ) : ℝ) /
      ((2 * k * c i + 1 : ℕ) : ℝ)) atTop (nhds 1) := by
    intro i
    rcases Nat.eq_zero_or_pos (c i) with h | h
    · simp [h]
    · have hc : (0:ℝ) < c i := by exact_mod_cast h
      have hden : Tendsto (fun k : ℕ => ((2 * k * c i + 1 : ℕ) : ℝ)) atTop atTop := by
        push_cast
        apply tendsto_atTop_add_const_right
        exact (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ) < 2)).atTop_mul_const hc
      have h0 : Tendsto (fun k : ℕ => (2 * m * c i : ℝ) / ((2 * k * c i + 1 : ℕ) : ℝ)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop hden
      have h1 := (tendsto_const_nhds (x := (1:ℝ))).add h0
      rw [add_zero] at h1
      refine h1.congr (fun k => ?_)
      have hpos : ((2 * k * c i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      push_cast
      ring
  have h := tendsto_finset_prod (Finset.univ : Finset (Fin r)) (fun i _ => key i)
  simp only [Finset.prod_const_one] at h
  refine h.congr (fun k => ?_)
  rw [Nat.cast_prod, Nat.cast_prod, Finset.prod_div_distrib]

end GlobalTheory

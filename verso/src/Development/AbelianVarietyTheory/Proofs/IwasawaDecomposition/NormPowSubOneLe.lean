import Mathlib

universe u_1

namespace GlobalTheory.NormPowSubOne

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `h : ζ ^ (n + 1) - 1 = ζ * (ζ ^ n - 1) + (ζ - 1)` using `by ring`. Rewrite using `[h]`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)` and prove the remaining obligations. Rewrite using `[norm_mul, hζ, one_mul]`. Conclude with `ih`.
-/
theorem norm_pow_sub_one_le {K : Type u_1} [NormedField K] [IsUltrametricDist K] {ζ : K}
    (hζ : ‖ζ‖ = (1 : ℝ)) (a : ℕ) : ‖ζ ^ a - (1 : K)‖ ≤ ‖ζ - (1 : K)‖ := by
  induction a with
  | zero => simp
  | succ n ih =>
    have h : ζ ^ (n + 1) - 1 = ζ * (ζ ^ n - 1) + (ζ - 1) := by ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul, hζ, one_mul]
    exact ih

/- English proof (translation)
Introduce `hζ a` and use `norm_pow_sub_one_le hζ a`.
-/
theorem main : ∀ {K : Type u_1} [inst : NormedField K] [IsUltrametricDist K] {ζ : K},
    ‖ζ‖ = (1 : ℝ) → ∀ (a : ℕ), ‖ζ ^ a - (1 : K)‖ ≤ ‖ζ - (1 : K)‖ :=
  fun hζ a => norm_pow_sub_one_le hζ a

end GlobalTheory.NormPowSubOne

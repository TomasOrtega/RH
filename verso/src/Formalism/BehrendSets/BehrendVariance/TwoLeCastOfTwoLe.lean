import Formalism.BehrendSets.Statement

open Finset Real

noncomputable section

namespace Formalism.BehrendSets.Sums

end Formalism.BehrendSets.Sums

namespace Formalism.BehrendSets.Sums

/- English proof (translation)
Establish `hm0 : m ≠ 0` using `by positivity`. Establish `hK0 : K ≠ 0` using `by positivity`. Establish `hx : 2 ≤ m * K` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts.
-/
theorem linB_real (m K L : ℝ) (hm : 2 ≤ m) (hK : 1 ≤ K) (hL : 0 ≤ L) :
    L / (m * K - 1) ≤ 2 * L * (1 / K) / m := by
  have hm0 : m ≠ 0 := by positivity
  have hK0 : K ≠ 0 := by positivity
  have hx : 2 ≤ m * K := by nlinarith
  calc L / (m * K - 1) ≤ L / (m * K / 2) :=
        div_le_div_of_nonneg_left hL (by positivity) (by linarith)
    _ = 2 * L * (1 / K) / m := by
        field_simp

/- English proof (translation)
Establish `h : 1 ≤ M * (k + 1)` using `Nat.one_le_iff_ne_zero.2 (by positivity)`. Rewrite using `[Nat.cast_sub h]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem castB (M k : ℕ) (hM : 2 ≤ M) :
    (((M * (k + 1) - 1 : ℕ)) : ℝ) = (M : ℝ) * ((k : ℝ) + 1) - 1 := by
  have h : 1 ≤ M * (k + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  rw [Nat.cast_sub h]
  push_cast
  ring

/- English proof (translation)
Use `(Nat.cast_nonneg k : (0 : ℝ) ≤ k)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hK1 (k : ℕ) : (1 : ℝ) ≤ (k : ℝ) + 1 := by
  have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  linarith

/- English proof (translation)
Conclude with `hM` after adjusting the coercions.
-/
theorem two_le_cast_of_two_le (M : ℕ) (hM : 2 ≤ M) : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM

/- English proof (translation)
Rewrite using `[castB M k hM]`. Conclude with `linB_real _ _ _ (two_le_cast_of_two_le M hM) (hK1 k) hL`.
-/
theorem linB (M k : ℕ) (L : ℝ) (hM : 2 ≤ M) (hL : 0 ≤ L) :
    L / (((M * (k + 1) - 1 : ℕ)) : ℝ) ≤ 2 * L * (1 / ((k : ℝ) + 1)) / (M : ℝ) := by
  rw [castB M k hM]
  exact linB_real _ _ _ (two_le_cast_of_two_le M hM) (hK1 k) hL

end Formalism.BehrendSets.Sums

namespace Formalism.BehrendSets

open Sums

end Formalism.BehrendSets

namespace Formalism.BehrendSets.Sums

end Formalism.BehrendSets.Sums

namespace Formalism.BehrendSets

open Sums

end Formalism.BehrendSets

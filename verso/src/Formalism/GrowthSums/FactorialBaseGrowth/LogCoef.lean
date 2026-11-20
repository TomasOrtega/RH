import Formalism.GrowthSums.StatementC
import Formalism.GrowthSums.FactorialBaseGrowth.Harmonic

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.GrowthSums

/- English proof (translation)
Proceed by induction on `v with`. Consider the case `zero => norm_num`. Consider the case `succ n ih`. Establish `h1 : 1 ≤ 5 ^ n` using `Nat.one_le_pow n 5 (by norm_num)`. Rewrite using `[pow_succ]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem four_mul_add_two_le_three_mul_five_pow (v : ℕ) : 4 * v + 2 ≤ 3 * 5 ^ v := by
  induction v with
  | zero => norm_num
  | succ n ih =>
    have h1 : 1 ≤ 5 ^ n := Nat.one_le_pow n 5 (by norm_num)
    rw [pow_succ]
    omega

/- English proof (translation)
Establish `hv` using `four_mul_add_two_le_three_mul_five_pow (padicValNat p s)`. Establish `h1 : 5 ^ padicValNat p s ≤ p ^ padicValNat p s` using `Nat.pow_le_pow_left hp5 _`. Establish `h2 : p ^ padicValNat p s ≤ s` using `Nat.le_of_dvd (by omega) pow_padicValNat_dvd`. Use linear arithmetic over natural numbers and integers.
-/
theorem four_padicValNat_le (p s : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hs : 1 ≤ s) :
    4 * padicValNat p s + 2 ≤ 3 * s := by
  have hv := four_mul_add_two_le_three_mul_five_pow (padicValNat p s)
  have h1 : 5 ^ padicValNat p s ≤ p ^ padicValNat p s := Nat.pow_le_pow_left hp5 _
  have h2 : p ^ padicValNat p s ≤ s := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  omega

/- English proof (translation)
Introduce `p t s hp hp5 hs`. Use `Fact.mk hp` as an intermediate fact. Use `set X : ℚ := ((p ^ (t + 1) : ℕ) : ℚ) ^ s * (∑ y ∈ Ico 1 (p ^ (t + 1)), 1 / (y : ℚ) ^ s) with hX`. Establish `hH : (s : ℤ) ≤ padicValRat p X` using `padicValHarmonicPowerSum p t s hp`. Establish `hp1 : 1 < p ^ (t + 1)` using `Nat.one_lt_pow (Nat.succ_ne_zero t) hp.one_lt`.

Establish `hpos : 0 < X`. Apply `mul_pos` to reduce the goal to its premises. Establish `: (0 : ℚ) < ((p ^ (t + 1) : ℕ) : ℚ)` using `by exact_mod_cast (by omega : 0 < p ^ (t + 1))`. Check the signs of the components of the expression. Apply `Finset.sum_pos` to reduce the goal to its premises.

Introduce `i hi`. Establish `: 1 ≤ i` using `(Finset.mem_Ico.mp hi).1`. Establish `: (0 : ℚ) < (i : ℚ)` using `by exact_mod_cast (by omega : 0 < i)`. Check the signs of the components of the expression. Conclude with `⟨1, Finset.mem_Ico.mpr ⟨le_rfl, hp1⟩⟩`.

Establish `hs0 : (s : ℚ) ≠ 0` using `by exact_mod_cast (by omega : s ≠ 0)`. Establish `key : (s : ℤ) - (padicValNat p s : ℤ) ≤ padicValRat p (X / s)`. Rewrite using `[padicValRat.div (ne_of_gt hpos) hs0, padicValRat.of_nat]`. Use linear arithmetic over natural numbers and integers. Establish `hk : (s : ℝ) - (padicValNat p s : ℝ) ≤ ((padicValRat p (X / s) : ℤ) : ℝ)`.

Conclude with `key` after adjusting the coercions. Establish `h4 : 4 * (padicValNat p s : ℝ) + 2 ≤ 3 * (s : ℝ)`. Conclude with `four_padicValNat_le p s hp hp5 hs` after adjusting the coercions. Establish `hq : (4 : ℝ) ≤ (p : ℝ) - 1`. Establish `: (5 : ℝ) ≤ (p : ℝ)` using `by exact_mod_cast hp5`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hinv : 1 / ((p : ℝ) - 1) ≤ 1 / 4` using `one_div_le_one_div_of_le (by norm_num) hq`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem padicValHarmonicPowerSumDivLowerBound : LogCoefVal := by
  intro p t s hp hp5 hs
  have := Fact.mk hp
  set X : ℚ := ((p ^ (t + 1) : ℕ) : ℚ) ^ s * (∑ y ∈ Ico 1 (p ^ (t + 1)), 1 / (y : ℚ) ^ s) with hX
  have hH : (s : ℤ) ≤ padicValRat p X := padicValHarmonicPowerSum p t s hp
  have hp1 : 1 < p ^ (t + 1) := Nat.one_lt_pow (Nat.succ_ne_zero t) hp.one_lt
  have hpos : 0 < X := by
    apply mul_pos
    · have : (0 : ℚ) < ((p ^ (t + 1) : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < p ^ (t + 1))
      positivity
    · apply Finset.sum_pos
      · intro i hi
        have : 1 ≤ i := (Finset.mem_Ico.mp hi).1
        have : (0 : ℚ) < (i : ℚ) := by exact_mod_cast (by omega : 0 < i)
        positivity
      · exact ⟨1, Finset.mem_Ico.mpr ⟨le_rfl, hp1⟩⟩
  have hs0 : (s : ℚ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
  have key : (s : ℤ) - (padicValNat p s : ℤ) ≤ padicValRat p (X / s) := by
    rw [padicValRat.div (ne_of_gt hpos) hs0, padicValRat.of_nat]
    omega
  have hk : (s : ℝ) - (padicValNat p s : ℝ) ≤ ((padicValRat p (X / s) : ℤ) : ℝ) := by
    exact_mod_cast key
  have h4 : 4 * (padicValNat p s : ℝ) + 2 ≤ 3 * (s : ℝ) := by
    exact_mod_cast four_padicValNat_le p s hp hp5 hs
  have hq : (4 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
    linarith
  have hinv : 1 / ((p : ℝ) - 1) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hq
  linarith

end Formalism.GrowthSums

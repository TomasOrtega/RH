import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions

open Finset Filter Topology ArithmeticFunction
open scoped ENNReal

namespace Formalism.HermitianLattices.GL2a2

open Formalism.HermitianLattices.GL2PrimeSums

/- English proof (translation)
Introduce `q n hq hn`. Establish `hqo : Odd q` using `by rw [Nat.odd_iff]; omega`. Rewrite using `[← neg_one_mul, jacobiSym.mul_left, jacobiSym.at_neg_one hn]`. Break down `Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hn) with h1 | h3` into its components or cases. Rewrite using `[jacobiSym.quadratic_reciprocity_one_mod_four' hqo h1]`.

Rewrite using `[ZMod.χ₄_nat_one_mod_four h1, one_mul]`. Rewrite using `[jacobiSym.quadratic_reciprocity_three_mod_four hq h3]`. Rewrite using `[ZMod.χ₄_nat_three_mod_four h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kronecker_odd : KronOdd := by
  intro q n hq hn
  have hqo : Odd q := by rw [Nat.odd_iff]; omega
  rw [← neg_one_mul, jacobiSym.mul_left, jacobiSym.at_neg_one hn]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hn) with h1 | h3
  · rw [jacobiSym.quadratic_reciprocity_one_mod_four' hqo h1]
    rw [ZMod.χ₄_nat_one_mod_four h1, one_mul]
  · rw [jacobiSym.quadratic_reciprocity_three_mod_four hq h3]
    rw [ZMod.χ₄_nat_three_mod_four h3]; ring

/- English proof (translation)
Introduce `q hq`. Establish `hqo : Odd q` using `by rw [Nat.odd_iff]; omega`. Rewrite using `[jacobiSym.at_two hqo]`. Establish `h8 : q % 8 = 3 ∨ q % 8 = 7` using `by omega`. Establish `: ((q : ℕ) : ZMod 8) = ((q % 8 : ℕ) : ZMod 8)` using `by simp`.

Use `push_cast`. Rewrite using `[this]`. Apply the tactic sequence `rcases h8 with h | h <;> rw [h] <;> decide`.
-/
theorem kronecker_two : KronTwo := by
  intro q hq
  have hqo : Odd q := by rw [Nat.odd_iff]; omega
  rw [jacobiSym.at_two hqo]
  have h8 : q % 8 = 3 ∨ q % 8 = 7 := by omega
  have : ((q : ℕ) : ZMod 8) = ((q % 8 : ℕ) : ZMod 8) := by simp
  push_cast
  rw [this]
  rcases h8 with h | h <;> rw [h] <;> decide

end Formalism.HermitianLattices.GL2a2

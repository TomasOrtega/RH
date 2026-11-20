import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

/- English proof (translation)
Take `⟨a, b, c, d, h⟩` from `Nat.sum_four_squares m`. Establish `h' : (m : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2`. Rewrite using `[← h]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨!![(a : ℤ), -b, -c, -d; b, a, -d, c; c, d, a, -b; d, -c, b, a], ?_⟩` and prove the remaining obligations. Rewrite using `[h']`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, Matrix.one_apply] <;> ring`.
-/
theorem exists_quaternion_matrix (m : ℕ) : ∃ A : Matrix (Fin 4) (Fin 4) ℤ,
    A.transpose * A = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares m
  have h' : (m : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2 := by
    rw [← h]; push_cast; ring
  refine ⟨!![(a : ℤ), -b, -c, -d; b, a, -d, c; c, d, a, -b; d, -c, b, a], ?_⟩
  rw [h']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, Matrix.one_apply] <;> ring

/- English proof (translation)
Introduce `g p hg hp`. Use `choose al hal using exists_quaternion_matrix`. Establish `hp0` using `hp.pos`. Establish `hnd : ¬ p ∣ degProd g (4 * p) (g * (4 * p) + 1) (g * (4 * p) + 1 + p)`. Unfold `degProd`.

Rewrite using `[Prime.dvd_finset_prod_iff hp.prime]`. Introduce and unpack `⟨j, hj, hd⟩`. Establish `hj' : j ≤ g` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hj'`. Establish `e1 : (j + k) * (4 * p) + 1 - j * (4 * p) = p * (4 * k) + 1`.

Apply `Nat.sub_eq_of_eq_add` to reduce the goal to its premises. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (j + k) * (4 * p) + 1 + p - j * (4 * p) = p * (4 * k + 1) + 1`. Apply `Nat.sub_eq_of_eq_add` to reduce the goal to its premises. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hd` using `[e1, e2]`. Break down `(Nat.Prime.dvd_mul hp).mp hd with h | h` into its components or cases. Conclude with `hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_right _ _)).mp h))`. Conclude with `hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_right _ _)).mp h))`. Establish `hpos : 0 < degProd g (4 * p) (g * (4 * p) + 1) (g * (4 * p) + 1 + p)` using `Nat.pos_of_ne_zero fun h => hnd (h ▸ dvd_zero p)`.

Use `⟨4 * p, g * (4 * p) + 1, g * (4 * p) + 1 + p, al, ⟨by omega, by omega, by omega, hal⟩, hnd, hpos, ?_⟩` and prove the remaining obligations. Unfold `kaExp`. Establish `h1 : 0 < g * (4 * p) + 1 + p - (g * (4 * p) + 1)` using `by omega`. Establish `h2` using `Nat.factorial_pos g`. Apply `Nat.succ_le_of_lt` to reduce the goal to its premises.

Check the signs of the components of the expression.
-/
theorem exists_admissibleKeyNumericalData_prime_to : ∀ g p : ℕ, 1 ≤ g → p.Prime → ∃ (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ), admitted g n l l' al ∧ ¬ p ∣ degProd g n l l' ∧ 1 ≤ degProd g n l l' ∧ 1 ≤ kaExp g n l l' := by
  intro g p hg hp
  choose al hal using exists_quaternion_matrix
  have hp0 := hp.pos
  have hnd : ¬ p ∣ degProd g (4 * p) (g * (4 * p) + 1) (g * (4 * p) + 1 + p) := by
    unfold degProd
    rw [Prime.dvd_finset_prod_iff hp.prime]
    rintro ⟨j, hj, hd⟩
    have hj' : j ≤ g := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj'
    have e1 : (j + k) * (4 * p) + 1 - j * (4 * p) = p * (4 * k) + 1 := by
      apply Nat.sub_eq_of_eq_add; ring
    have e2 : (j + k) * (4 * p) + 1 + p - j * (4 * p) = p * (4 * k + 1) + 1 := by
      apply Nat.sub_eq_of_eq_add; ring
    rw [e1, e2] at hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
    · exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_right _ _)).mp h))
    · exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_right _ _)).mp h))
  have hpos : 0 < degProd g (4 * p) (g * (4 * p) + 1) (g * (4 * p) + 1 + p) :=
    Nat.pos_of_ne_zero fun h => hnd (h ▸ dvd_zero p)
  refine ⟨4 * p, g * (4 * p) + 1, g * (4 * p) + 1 + p, al, ⟨by omega, by omega, by omega, hal⟩,
    hnd, hpos, ?_⟩
  unfold kaExp
  have h1 : 0 < g * (4 * p) + 1 + p - (g * (4 * p) + 1) := by omega
  have h2 := Nat.factorial_pos g
  apply Nat.succ_le_of_lt
  positivity

end GlobalTheory.KeyKa

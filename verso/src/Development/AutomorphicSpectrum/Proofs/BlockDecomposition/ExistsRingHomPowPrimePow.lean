import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Frobenius

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem exists_ringHom_pow_prime_pow :
    ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A], (p : A) = 0 → ∀ k : ℕ,
      ∃ F : A →+* A, ∀ x, F x = x ^ p ^ k := by
  intro p hp A _ hpA k
  refine ⟨{ toFun := fun x => x ^ p ^ k
            map_one' := one_pow _
            map_mul' := fun x y => mul_pow x y _
            map_zero' := zero_pow (pow_ne_zero k hp.out.ne_zero)
            map_add' := fun x y => ?_ }, fun x => rfl⟩
  show (x + y) ^ p ^ k = x ^ p ^ k + y ^ p ^ k
  rw [add_pow_prime_pow_eq hp.out x y k, hpA]
  simp only [zero_mul, add_zero]

end GlobalTheory.CompanionTheory.Frobenius

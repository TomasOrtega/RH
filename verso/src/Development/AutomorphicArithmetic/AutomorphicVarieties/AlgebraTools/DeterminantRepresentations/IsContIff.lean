import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.AdicContIff

open Polynomial UpperTheory.V.W

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.AlgebraTools.Det.isContIff :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace G] (I : Ideal A), IsAdic I → ∀ D : GDet n A G,
    D.IsCont I ↔ ∀ i ≤ n, Continuous fun g : G => D.lam i (MonoidAlgebra.single g 1) := by
  intro n A G _ _ _ _ _ I hI D
  unfold GDet.IsCont
  simp only [UpperTheory.V.AlgebraTools.Det.adicContIff I hI]
  constructor
  · intro h i _
    exact h i
  · intro h i
    by_cases hi : i ≤ n
    · exact h i hi
    · have heq : (fun g : G => D.lam i (MonoidAlgebra.single g 1)) =
          fun g => (-1) ^ (i + n) * D.lam n (MonoidAlgebra.single g 1) := by
        funext g
        unfold GDet.lam
        rw [Nat.sub_eq_zero_of_le (not_le.mp hi).le, Nat.sub_self, ← mul_assoc, ← pow_add, add_assoc,
          ← two_mul, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
      rw [heq]
      exact continuous_const.mul (h n le_rfl)

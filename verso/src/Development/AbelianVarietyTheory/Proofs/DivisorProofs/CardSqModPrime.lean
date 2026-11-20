import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroSquaresSumEquivIcoModFourStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers.
-/
theorem card_sq_mod_prime : ∀ (p : ℕ), p.Prime → p % 4 = 3 →
    2 * Fintype.card (Sq p) + 1 = p ∧ Odd (Fintype.card (Sq p)) := by
  intro p hp h4
  obtain ⟨e, -⟩ := GlobalTheory.T.nonzeroSquares_sum_equiv_Ico_mod_four p hp h4
  have hc := Fintype.card_congr e
  rw [Fintype.card_sum] at hc
  have h2 : Fintype.card (Finset.Ico 1 p : Finset ℕ) = p - 1 := by
    simp
  rw [h2] at hc
  have hp2 := hp.two_le
  have hsum : 2 * Fintype.card (Sq p) + 1 = p := by omega
  refine ⟨hsum, ?_⟩
  rw [Nat.odd_iff]
  omega

end GlobalTheory.CMModel

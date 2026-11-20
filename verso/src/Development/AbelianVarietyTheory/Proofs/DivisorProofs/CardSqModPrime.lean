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
Introduce `p hp h4`. Take `⟨e, -⟩` from `GlobalTheory.T.nonzeroSquares_sum_equiv_Ico_mod_four p hp h4`. Establish `hc` using `Fintype.card_congr e`. Rewrite `hc` using `[Fintype.card_sum]`. Establish `h2 : Fintype.card (Finset.Ico 1 p : Finset ℕ) = p - 1`.

Simplify using the standard rewrite rules. Rewrite `hc` using `[h2]`. Establish `hp2` using `hp.two_le`. Establish `hsum : 2 * Fintype.card (Sq p) + 1 = p` using `by omega`. Use `⟨hsum, ?_⟩` and prove the remaining obligations.

Rewrite using `[Nat.odd_iff]`. Use linear arithmetic over natural numbers and integers.
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

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem Coinv.monomial_staircase_eq (f N : ℕ) :
    (monomial (Coinv.staircase f N) (1 : ℚ) : RootRing f N) =
      ∏ τ : Fin f, ∏ i : Fin N, X (τ, i) ^ (i : ℕ) := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_prod_type]
  simp [Coinv.staircase]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Coinv.psumIdeal_rat_eq (f N : ℕ) :
    Coinv.psumIdeal ℚ f N =
      Ideal.span {P | ∃ k τ, 1 ≤ k ∧ k ≤ N ∧ P = blockPowerSum f N k τ} := rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem CoinvariantTopDegree.proof (h1 : CoinvAtTop.Statement) : CoinvariantTopDegree.Statement := by
  intro f N H hH
  obtain ⟨c, hc⟩ := h1 ℚ f N H hH
  refine ⟨c, ?_⟩
  rw [← Coinv.monomial_staircase_eq, ← Coinv.psumIdeal_rat_eq]
  exact hc

end

end GroundTheory.Heights₂.Heights.RestTerms

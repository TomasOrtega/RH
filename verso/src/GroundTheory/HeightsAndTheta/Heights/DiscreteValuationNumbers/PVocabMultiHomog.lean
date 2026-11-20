import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBridge
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem weight_blockWeight_apply {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) m k = ∑ i, m ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [blockWeight, Pi.single_apply]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem VocabMultiHomog.proof : VocabMultiHomog.Statement := by
  intro R _ K _ _ ι _ s a
  constructor
  · intro h d hd
    funext k
    rw [weight_blockWeight_apply]
    exact h d (MvPolynomial.mem_support_iff.mpr hd) k
  · intro h m hm k
    rw [← weight_blockWeight_apply]
    exact congrFun (h (MvPolynomial.mem_support_iff.mp hm)) k

end

end GroundTheory.Heights₂.Heights.NumbersDVR

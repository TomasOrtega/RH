import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBridge
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]`. Simplify using `[blockWeight, Pi.single_apply]`.
-/
theorem weight_blockWeight_apply {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) m k = ∑ i, m ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [blockWeight, Pi.single_apply]

/- English proof (translation)
Introduce `R _ K _ _ ι _ s a`. Prove the components needed by the constructor for the conclusion. Introduce `h d hd`. Use function extensionality and compare the values at `k`. Rewrite using `[weight_blockWeight_apply]`.

Conclude with `h d (MvPolynomial.mem_support_iff.mpr hd) k`. Introduce `h m hm k`. Rewrite using `[← weight_blockWeight_apply]`. Conclude with `congrFun (h (MvPolynomial.mem_support_iff.mp hm)) k`.
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

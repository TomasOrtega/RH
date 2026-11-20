import Mathlib
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.RatHerm
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.LocBasis
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.IdxChange

open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

namespace ConjugateWeightLattice

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem gen_iff (p : Ideal (𝓞 K)) (s : 𝓞 K) :
    (s ∉ p ∧ ∀ t : 𝓞 K, algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K s) → t ∉ p) ↔
      (s ∉ p ∧ cO K s ∉ p) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2 _ rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun t ht => ?_⟩
    have : t = cO K s := RingOfIntegers.ext ht
    rw [this]
    exact h2

end ConjugateWeightLattice

open ConjugateWeightLattice

end Formalism.DivisionValues

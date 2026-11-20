import Mathlib
import Formalism.JacquetSubsetSums.JacquetSubsetSum
import Formalism.JacquetSubsetSums.SeparationTR

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Prove the first alternative.

Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem signEven : Formalism.PacketSums.SignEven := by
  intro p q h
  apply Even.neg_one_pow
  rw [Nat.even_mul]
  rcases Nat.even_or_odd p with hp | hp
  · exact Or.inl hp
  · right
    rcases Nat.even_or_odd q with hq | hq
    · exact hq
    · exact absurd (hp.add_odd hq) (Nat.not_even_iff_odd.mpr h)

end GlobalTheory

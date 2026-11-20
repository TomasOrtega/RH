import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

/- English proof (translation)
Introduce `A _ J Q _ N hJQ hJ hQ`. Assume the negation of the conclusion as `hmin`. Take `⟨W, hW, hWQ⟩` from `Ideal.exists_minimalPrimes_le hJQ`. Establish `hWne : W ≠ Q` using `fun h => hmin (h ▸ hW)`. Establish `hWlt : W < Q` using `lt_of_le_of_ne hWQ hWne`.

Establish `: W.IsPrime` using `hW.1.1`. Establish `hJW : J ≤ W` using `hW.1.2`. Establish `h2 : ringKrullDim (A ⧸ Q) + 1 ≤ ringKrullDim (A ⧸ W)` using `h1 A W Q hWlt`. Establish `h3 : ringKrullDim (A ⧸ W) ≤ ringKrullDim (A ⧸ J)` using `ringKrullDim_le_of_surjective (Ideal.Quotient.factor hJW) (Ideal.Quotient.factor_surjective hJW)`. Establish `h4 : ((N : ℕ) : WithBot ℕ∞) + 1 ≤ ringKrullDim (A ⧸ Q) + 1` using `add_le_add (not_lt.mp hQ) le_rfl`.

Establish `h5 : ((N + 1 : ℕ) : WithBot ℕ∞) = ((N : ℕ) : WithBot ℕ∞) + 1` using `Nat.cast_succ N`. Conclude with `lt_irrefl _ (lt_of_le_of_lt (h5 ▸ h4.trans (h2.trans h3)) hJ)`.
-/
theorem TopDimMinimal.proof (h1 : DimStrictDrop.Statement.{u}) : TopDimMinimal.Statement.{u} := by
  intro A _ J Q _ N hJQ hJ hQ
  by_contra hmin
  obtain ⟨W, hW, hWQ⟩ := Ideal.exists_minimalPrimes_le hJQ
  have hWne : W ≠ Q := fun h => hmin (h ▸ hW)
  have hWlt : W < Q := lt_of_le_of_ne hWQ hWne
  have : W.IsPrime := hW.1.1
  have hJW : J ≤ W := hW.1.2
  have h2 : ringKrullDim (A ⧸ Q) + 1 ≤ ringKrullDim (A ⧸ W) := h1 A W Q hWlt
  have h3 : ringKrullDim (A ⧸ W) ≤ ringKrullDim (A ⧸ J) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hJW) (Ideal.Quotient.factor_surjective hJW)
  have h4 : ((N : ℕ) : WithBot ℕ∞) + 1 ≤ ringKrullDim (A ⧸ Q) + 1 :=
    add_le_add (not_lt.mp hQ) le_rfl
  have h5 : ((N + 1 : ℕ) : WithBot ℕ∞) = ((N : ℕ) : WithBot ℕ∞) + 1 := Nat.cast_succ N
  exact lt_irrefl _ (lt_of_le_of_lt (h5 ▸ h4.trans (h2.trans h3)) hJ)

end GroundTheory.Heights₂.Heights.NumbersDVR

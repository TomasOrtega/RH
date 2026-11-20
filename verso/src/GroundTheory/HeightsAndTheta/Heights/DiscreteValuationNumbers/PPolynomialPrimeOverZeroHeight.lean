import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsDimensionInequalitySteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open Polynomial

attribute [local instance] Polynomial.algebra Polynomial.isLocalization in

/- English proof (translation)
Introduce `D _ _ Q _ hQ`. Set `K` to `FractionRing D`. Establish `disj : Disjoint ((nonZeroDivisors D).map (C : D →+* D[X]) : Set D[X]) (Q : Set D[X])`. Use `Set.disjoint_left.mpr fun a ⟨b, hb⟩ ha ↦ ?_` and prove the remaining obligations. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb.1`.

Apply `hb0` to reduce the goal to its premises. Establish `: b ∈ Q.comap (C : D →+* D[X])`. Rewrite using `[Ideal.mem_comap]`. Simplify `ha` using `[hb.2]`. Rewrite `this` using `[hQ, Ideal.mem_bot]`. Then use the resulting hypothesis.

Establish `hK : ringKrullDim K[X] = 1` using `IsPrincipalIdealRing.ringKrullDim_eq_one K[X] (Polynomial.not_isField K)`. Establish `h` using `IsLocalization.height_map_of_disjoint ((nonZeroDivisors D).map (C : D →+* D[X])) (S := K[X]) Q disj`. Establish `hP : (Q.map (algebraMap D[X] K[X])).IsPrime` using `IsLocalization.isPrime_of_isPrime_disjoint ((nonZeroDivisors D).map (C : D →+* D[X])) K[X] Q ‹_› disj`. Establish `hle : ((Q.map (algebraMap D[X] K[X])).height : WithBot ℕ∞) ≤ 1` using `hK ▸ Ideal.height_le_ringKrullDim_of_isPrime`. Rewrite `hle` using `[h]`.

Conclude with `hle` after adjusting the coercions.
-/
theorem PolynomialPrimeOverZeroHeight.proof : PolynomialPrimeOverZeroHeight.Statement := by
  intro D _ _ Q _ hQ
  let K := FractionRing D
  have disj : Disjoint ((nonZeroDivisors D).map (C : D →+* D[X]) : Set D[X]) (Q : Set D[X]) := by
    refine Set.disjoint_left.mpr fun a ⟨b, hb⟩ ha ↦ ?_
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb.1
    apply hb0
    have : b ∈ Q.comap (C : D →+* D[X]) := by
      rw [Ideal.mem_comap]
      simpa [hb.2] using ha
    rwa [hQ, Ideal.mem_bot] at this
  have hK : ringKrullDim K[X] = 1 :=
    IsPrincipalIdealRing.ringKrullDim_eq_one K[X] (Polynomial.not_isField K)
  have h := IsLocalization.height_map_of_disjoint ((nonZeroDivisors D).map (C : D →+* D[X]))
    (S := K[X]) Q disj
  have hP : (Q.map (algebraMap D[X] K[X])).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint ((nonZeroDivisors D).map (C : D →+* D[X])) K[X] Q
      ‹_› disj
  have hle : ((Q.map (algebraMap D[X] K[X])).height : WithBot ℕ∞) ≤ 1 :=
    hK ▸ Ideal.height_le_ringKrullDim_of_isPrime
  rw [h] at hle
  exact_mod_cast hle

end GroundTheory.Heights₂.Heights.NumbersDVR

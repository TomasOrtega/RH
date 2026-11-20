import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.IsFlagIntegralOne
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagBasic
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.IsPowerSumDecompositionHomogeneousComponent
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagIntegralRealEqMulDdConst
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

namespace DividedDifferenceVandermonde

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem ringToReal_eq_map (f j k : ℕ) (Φ : RootRing f (j + k)) :
    rootRingToReal f (j + k) j k rfl Φ = map (algebraMap ℚ ℝ) Φ := by
  simp [rootRingToReal]

/- English proof (translation)
Substitute using the available equality. Rewrite the conclusion using the stated equalities.
-/
theorem flagIntegral_eq_mul_ddConst (f N j k : ℕ) (h : N = j + k) (Φ : RootRing f N) :
    (flagIntegral f N Φ : ℝ) =
      FlagEq.stairConst f (j + k) * IndefiniteRowSideFullHecke.RestTerms.ddConst f j k (rootRingToReal f N j k h Φ) := by
  subst h
  rw [← flagIntegralReal_map, flagIntegralReal_eq_mul_ddConst, ringToReal_eq_map]

end DividedDifferenceVandermonde

open DividedDifferenceVandermonde

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem FlagIntegralKillsPowerSums.intersectionNumber_baseChange : FlagIntegralKillsPowerSums.Statement := by
  intro f N k τ G hk _
  have h := flagIntegral_eq_mul_ddConst f N N 0 rfl (blockPowerSum f N k τ * G)
  rw [map_mul, rootRingToReal_blockPowerSum, FlagEq.ddConst_psumAt_mul _ _ _ _ _ _ hk,
    mul_zero] at h
  exact_mod_cast h

end

end GroundTheory.Heights₂.Heights.RestTerms

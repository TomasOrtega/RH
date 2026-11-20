import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowDivisibilityOfDescentDatum
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImagePolynomialAction
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.divisible_of_BKDat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FPrimePowDivisibilityOfDescentDatum.lean&line=88#L88)
-/
theorem _root_.GlobalTheory.T.prime_pow_divisibility_of_descentDatum : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Divisible D := by
  first | exact @GlobalTheory.divisible_of_BKDat | exact GlobalTheory.divisible_of_BKDat | (intros; apply GlobalTheory.divisible_of_BKDat <;> assumption)

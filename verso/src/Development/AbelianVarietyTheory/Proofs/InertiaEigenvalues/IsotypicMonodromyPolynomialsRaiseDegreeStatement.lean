import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicMonodromyPolynomialsRaiseDegree
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImageStableDegreeBounds
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DegreeRaise.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsotypicMonodromyPolynomialsRaiseDegree.lean&line=218#L218)
-/
theorem _root_.GlobalTheory.T.isotypic_monodromy_polynomials_raise_degree : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a], GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.Degrees O K l e a := by
  first | exact @GlobalTheory.DegreeRaise.main | exact GlobalTheory.DegreeRaise.main | (intros; apply GlobalTheory.DegreeRaise.main <;> assumption)

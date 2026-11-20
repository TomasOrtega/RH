import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompleteSpaceOfFinitePadicIntUnitBall
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCompleteSpaceOfFinitePadicIntUnitBall.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.completeSpace_of_finite_padicInt_unitBall : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K], CompleteSpace K := by
  first | exact @GlobalTheory.CoeffComplete.completeSpace_of_finite_unitBall | exact GlobalTheory.CoeffComplete.completeSpace_of_finite_unitBall | (intros; apply GlobalTheory.CoeffComplete.completeSpace_of_finite_unitBall <;> assumption)

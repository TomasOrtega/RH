import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAdicCompleteTwistedInvariantLattice
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BK.BKDat.isAdicComplete_Y'` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsAdicCompleteTwistedInvariantLattice.lean&line=201#L201)
-/
theorem _root_.GlobalTheory.T.isAdicComplete_twistedInvariantLattice : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), IsAdicComplete (Ideal.span {(l : O)}) D.Y' := by
  first | exact @GlobalTheory.BK.BKDat.isAdicComplete_Y' | exact GlobalTheory.BK.BKDat.isAdicComplete_Y' | (intros; apply GlobalTheory.BK.BKDat.isAdicComplete_Y' <;> assumption)

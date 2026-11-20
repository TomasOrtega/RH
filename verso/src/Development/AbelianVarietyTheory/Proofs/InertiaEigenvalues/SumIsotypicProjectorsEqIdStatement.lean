import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumIsotypicProjectorsEqId
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiagScaleApply
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CokerL.sum_isoProj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FSumIsotypicProjectorsEqId.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.sum_isotypicProjectors_eq_id : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι) (Δ : Descent P) (v : Vec K a ι), ∑ c : ZMod e, GlobalTheory.CokerL.isoProj Δ c v = v := by
  first | exact @GlobalTheory.CokerL.sum_isoProj | exact GlobalTheory.CokerL.sum_isoProj | (intros; apply GlobalTheory.CokerL.sum_isoProj <;> assumption)

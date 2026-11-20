import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicProjectorMemBreuilKisinLattice
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiagScaleApply
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsotypicProjectorMemBreuilKisinLattice.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.isotypicProjector_mem_breuilKisinLattice : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι) (Δ : Descent P) (c : ZMod e) (v : Vec K a ι), v ∈ P.L → GlobalTheory.CokerL.isoProj Δ c v ∈ P.L := by
  first | exact @GlobalTheory.CokerL.isoProj_mem_L | exact GlobalTheory.CokerL.isoProj_mem_L | (intros; apply GlobalTheory.CokerL.isoProj_mem_L <;> assumption)

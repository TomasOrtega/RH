import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicProjectorMemIsotypicPartExplicit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiagScaleApply
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CokerL.isoProj_mem_isotypic'` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsotypicProjectorMemIsotypicPartExplicit.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.isotypicProjector_mem_isotypicPart_explicit : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι) (Δ : Descent P) (c : ZMod e) (v : Vec K a ι), GlobalTheory.CokerL.isoProj Δ c v ∈ Δ.isotypic c := by
  first | exact @GlobalTheory.CokerL.isoProj_mem_isotypic' | exact GlobalTheory.CokerL.isoProj_mem_isotypic' | (intros; apply GlobalTheory.CokerL.isoProj_mem_isotypic' <;> assumption)

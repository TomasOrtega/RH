import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianTemperateGrowth
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
open GlobalTheory.ArchSch
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.QuadPhase.hasTemperateGrowth_quadPhase` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGaussianTemperateGrowth.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.gaussian_temperate_growth : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : LinearMap.BilinForm ℝ V)
    (L : V →ₗ[ℝ] ℝ) (c : ℝ), Function.HasTemperateGrowth (fun x : V => ech (Q x x + L x + c)) := by
  first | exact @GlobalTheory.QuadPhase.hasTemperateGrowth_quadPhase | exact GlobalTheory.QuadPhase.hasTemperateGrowth_quadPhase | (intros; apply GlobalTheory.QuadPhase.hasTemperateGrowth_quadPhase <;> assumption)

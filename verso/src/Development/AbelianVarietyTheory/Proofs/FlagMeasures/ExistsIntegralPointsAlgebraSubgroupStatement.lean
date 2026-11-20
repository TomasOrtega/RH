import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralPointsAlgebraSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsIntegralPointsAlgebraSubgroup.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.exists_integral_points_algebra_subgroup : ∀ (I : AutInst) (xf : I.Gf) (A : InfinitePlace I.F → Submodule ℂ (Matrix (Fin I.n) (Fin I.n) ℂ)), (∀ v, ∀ X ∈ A v, ∀ Y ∈ A v, X * Y ∈ A v) → (∀ v, ∀ X ∈ A v, Formalism.REAL.Jm (I.ε v) * Xᴴ * Formalism.REAL.Jm (I.ε v) ∈ A v) → ∃ Γ : Subgroup I.Ginf, (Γ : Set I.Ginf) = {g | g ∈ latGroup I xf ∧ ∀ v, uMat (g v) - 1 ∈ A v} := by
  first | exact @GlobalTheory.AlgCutSubgroup.exists_subgroup | exact GlobalTheory.AlgCutSubgroup.exists_subgroup | (intros; apply GlobalTheory.AlgCutSubgroup.exists_subgroup <;> assumption)

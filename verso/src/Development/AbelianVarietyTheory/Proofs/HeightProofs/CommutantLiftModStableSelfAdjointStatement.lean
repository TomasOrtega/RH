import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommutantLiftModStableSelfAdjoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.matrix_commutant_lift_mod_stable` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FCommutantLiftModStableSelfAdjoint.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.commutant_lift_mod_stable_selfAdjoint : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : Set (Matrix ι ι ℂ)) (N : Submodule ℂ (Matrix ι ι ℂ)), (∀ x ∈ S, xᴴ ∈ S) → (∀ x ∈ S, ∀ y ∈ N, x * y - y * x ∈ N) → ∀ M : Matrix ι ι ℂ, (∀ x ∈ S, x * M - M * x ∈ N) → ∃ M₀ : Matrix ι ι ℂ, M - M₀ ∈ N ∧ ∀ x ∈ S, x * M₀ = M₀ * x := by
  first | exact @GlobalTheory.matrix_commutant_lift_mod_stable | exact GlobalTheory.matrix_commutant_lift_mod_stable | (intros; apply GlobalTheory.matrix_commutant_lift_mod_stable <;> assumption)

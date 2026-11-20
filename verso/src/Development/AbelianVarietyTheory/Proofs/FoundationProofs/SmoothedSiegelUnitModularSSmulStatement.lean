import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitModularSSmul
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Sieg.sg_S` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSmoothedSiegelUnitModularSSmul.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.smoothedSiegelUnit_modularS_smul : ∀ (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), admitted c x → sg c x (ModularGroup.S • τ) = sg c (act x ModularGroup.S) τ := by
  first | exact @GlobalTheory.Sieg.sg_S | exact GlobalTheory.Sieg.sg_S | (intros; apply GlobalTheory.Sieg.sg_S <;> assumption)

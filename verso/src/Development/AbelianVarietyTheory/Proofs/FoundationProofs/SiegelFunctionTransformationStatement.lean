import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionTransformation
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSiegelFunctionTransformation.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.siegel_function_transformation : ∀ (c : ℕ) (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) (τ : ℍ), admitted c x → sg c x (γ • τ) = sg c (act x γ) τ := by
  first | exact @GlobalTheory.Sieg.sg_smul | exact GlobalTheory.Sieg.sg_smul | (intros; apply GlobalTheory.Sieg.sg_smul <;> assumption)

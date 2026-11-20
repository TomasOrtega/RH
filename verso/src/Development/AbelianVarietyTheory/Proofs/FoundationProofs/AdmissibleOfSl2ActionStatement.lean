import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleOfSl2Action
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FAdmissibleOfSl2Action.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.admissible_of_sl2_action : ∀ (c : ℕ) (x : Fin 2 → ℚ) (γ : SL(2, ℤ)), admitted c x → admitted c (act x γ) := by
  first | exact @GlobalTheory.Sieg.admissible_act_SL2 | exact GlobalTheory.Sieg.admissible_act_SL2 | (intros; apply GlobalTheory.Sieg.admissible_act_SL2 <;> assumption)

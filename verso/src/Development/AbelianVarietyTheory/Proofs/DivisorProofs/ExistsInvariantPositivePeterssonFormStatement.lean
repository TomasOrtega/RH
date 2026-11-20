import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantPositivePeterssonForm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DefU.Petersson.exists_invariant_pos_form` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsInvariantPositivePeterssonForm.lean&line=97#L97)
-/
theorem _root_.GlobalTheory.T.exists_invariant_positive_petersson_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∃ B : GlobalTheory.DefU.autU E n →ₗ⋆[ℂ] GlobalTheory.DefU.autU E n →ₗ[ℂ] ℂ, (∀ u v, star (B u v) = B v u) ∧ (∀ v, 0 ≤ (B v v).re) ∧ (∀ v, B v v = 0 → v = 0) ∧ ∀ g u v, B (GlobalTheory.DefU.autRep E n g u) (GlobalTheory.DefU.autRep E n g v) = B u v := by
  first | exact @GlobalTheory.DefU.Petersson.exists_invariant_pos_form | exact GlobalTheory.DefU.Petersson.exists_invariant_pos_form | (intros; apply GlobalTheory.DefU.Petersson.exists_invariant_pos_form <;> assumption)

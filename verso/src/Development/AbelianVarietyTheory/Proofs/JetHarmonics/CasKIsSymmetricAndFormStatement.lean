import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasKIsSymmetricAndForm
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.casK_isSymmetric_and_form` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FCasKIsSymmetricAndForm.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.casK_isSymmetric_and_inner_re_eq : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M), KUnit ε E → LinearMap.IsSymmetric (CasK ε E) ∧ ∀ x, (⟪x, CasK ε E x⟫_ℂ).re = ∑ a, ∑ b, if ε a = ε b then ‖E a b x‖ ^ 2 else 0 := by
  first | exact @GlobalTheory.casK_isSymmetric_and_form | exact GlobalTheory.casK_isSymmetric_and_form | (intros; apply GlobalTheory.casK_isSymmetric_and_form <;> assumption)

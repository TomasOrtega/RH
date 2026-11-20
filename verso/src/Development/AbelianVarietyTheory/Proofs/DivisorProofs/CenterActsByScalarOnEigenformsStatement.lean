import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CenterActsByScalarOnEigenforms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCenterActsByScalarOnEigenforms.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.center_acts_by_scalar_on_eigenforms : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (c : (E →+* ℂ) → ℂ → ℂ) (z : Module.End ℂ (GlobalTheory.CuspRep.Sm E a)), z ∈ GlobalTheory.CuspRep.Zalg E a → ∃ s : ℂ, ∀ φ : GlobalTheory.CuspRep.Sm E a, (∀ τ u, GlobalTheory.CuspRep.cap τ u φ = c τ u • φ) → z φ = s • φ := by
  first | exact @GlobalTheory.CuspRep.Zalg_acts_by_scalar | exact GlobalTheory.CuspRep.Zalg_acts_by_scalar | (intros; apply GlobalTheory.CuspRep.Zalg_acts_by_scalar <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinDeltaQExpansionIntegrality
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEisensteinDeltaQExpansionIntegrality.lean&line=71#L71)
-/
theorem _root_.GlobalTheory.T.eisenstein_delta_qExpansion_integrality : ∀ (N : ℕ), 0 < N → ∀ F : ℍ → ℂ, (F = ⇑E₄ ∨ F = ⇑E₆ ∨ F = DD) → (∃ a : ℕ → ℤ, HasQ N F fun n => (a n : ℂ)) ∧ (∀ R : Subring ℂ, QAll (· ∈ R) N F) ∧ ∀ g : ℂ ≃+* ℂ, QConj g N F F := by
  first | exact @GlobalTheory.QFam.eis_q | exact GlobalTheory.QFam.eis_q | (intros; apply GlobalTheory.QFam.eis_q <;> assumption)

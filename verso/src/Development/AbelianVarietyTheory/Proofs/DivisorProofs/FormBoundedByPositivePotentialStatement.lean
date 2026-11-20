import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormBoundedByPositivePotential
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFormBoundedByPositivePotential.lean&line=158#L158)
-/
theorem _root_.GlobalTheory.T.form_bounded_by_positive_potential : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (P Q : LocPot X), IsPotential A P → IsPotential A Q → IsPosPot A Q → ∃ C : ℝ, 0 < C ∧ ∀ ψ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ → ∀ z ∈ ψ.target, ∀ w, |formAt ψ P z w| ≤ C * formAt ψ Q z w := by
  first | exact @GlobalTheory.ChernCompare.chern_le_kahler | exact GlobalTheory.ChernCompare.chern_le_kahler | (intros; apply GlobalTheory.ChernCompare.chern_le_kahler <;> assumption)

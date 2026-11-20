import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormAtContinuous
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.formAt_continuousOn` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFormAtContinuous.lean&line=72#L72)
-/
theorem _root_.GlobalTheory.T.form_at_continuous : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : LocPot X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)), IsPotential A P → IsCompatChart A ψ → ContinuousOn (fun p : (Fin e → ℂ) × (Fin e → ℂ) => formAt ψ P p.1 p.2) (ψ.target ×ˢ Set.univ) := by
  first | exact @GlobalTheory.formAt_continuousOn | exact GlobalTheory.formAt_continuousOn | (intros; apply GlobalTheory.formAt_continuousOn <;> assumption)

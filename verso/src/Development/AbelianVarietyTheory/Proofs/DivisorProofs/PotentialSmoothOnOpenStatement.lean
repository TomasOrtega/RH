import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothOnOpen
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isPotentialOn_contDiffAt_two_compatChart` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPotentialSmoothOnOpen.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.potential_smooth_on_open : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : LocPot X) (O : Set X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (z : Fin e → ℂ), IsOpen O → IsPotentialOn A O P → IsCompatChart A ψ → z ∈ ψ.target → ψ.symm z ∈ O → ContDiffAt ℝ 2 (P.φ (ψ.symm z) ∘ ψ.symm) z := by
  first | exact @GlobalTheory.isPotentialOn_contDiffAt_two_compatChart | exact GlobalTheory.isPotentialOn_contDiffAt_two_compatChart | (intros; apply GlobalTheory.isPotentialOn_contDiffAt_two_compatChart <;> assumption)

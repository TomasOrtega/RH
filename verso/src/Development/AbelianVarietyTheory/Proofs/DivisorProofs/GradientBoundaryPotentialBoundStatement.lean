import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradientBoundaryPotentialBound
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGradientBoundaryPotentialBound.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.gradient_boundary_potential_bound : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (K : LocPot X) {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X), IsPotential A K → IsPosPot A K → IsBoundary A L s D → ∃ C : ℝ, 0 < C ∧ ∀ (i : Fin m) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)), IsCompatChart A ψ → ∀ z ∈ ψ.target, ψ.symm z ∉ D i → ∀ w, gradSqAt ψ (rComp L s i) z w ≤ C * Real.exp (rComp L s i (ψ.symm z)) * formAt ψ K z w := by
  first | exact @GlobalTheory.PoincareGrad.gradSq_le_exp_mul_form | exact GlobalTheory.PoincareGrad.gradSq_le_exp_mul_form | (intros; apply GlobalTheory.PoincareGrad.gradSq_le_exp_mul_form <;> assumption)

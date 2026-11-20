import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcBoundaryPotentialEqForm
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDdcBoundaryPotentialEqForm.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.ddc_boundary_potential_eq_form : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X), IsBoundary A L s D → ∀ (i : Fin m) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)), IsCompatChart A ψ → ∀ z ∈ ψ.target, ψ.symm z ∉ D i → ∀ w, ddcAt ψ (rComp L s i) z w = formAt ψ (L i) z w := by
  first | exact @GlobalTheory.LeviChern.ddcAt_rComp_eq_formAt | exact GlobalTheory.LeviChern.ddcAt_rComp_eq_formAt | (intros; apply GlobalTheory.LeviChern.ddcAt_rComp_eq_formAt <;> assumption)
